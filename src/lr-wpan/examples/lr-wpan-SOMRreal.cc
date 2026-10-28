#include "ns3/core-module.h"
#include "ns3/lr-wpan-module.h"
#include "ns3/mobility-module.h"
#include "ns3/network-module.h"
#include "ns3/propagation-module.h"
#include "ns3/spectrum-module.h"
#include "ns3/internet-module.h"

#include <cmath>
#include <fstream>
#include <iostream>
#include <limits>
#include <map>
#include <random>
#include <sstream>
#include <algorithm>
#include <vector>

using namespace ns3;
using namespace ns3::lrwpan;

NodeContainer nodes;
NodeContainer coordinators;

// 電波伝搬モデルの環境定数
static const double ENV_TX_POWER = 0.0;
static const double ENV_REF_LOSS = 40.0;   
static const double ENV_EXPONENT = 2.0;

// トンネル坑道内の対数正規シャドウイング（RSSI揺らぎ）の標準偏差 σ [dB]
static double g_shadowingStdDb = 2.75;
static Ptr<NormalRandomVariable> g_rssiNoiseGenerator;

// ==========================================
// 【カプセル化】各ノードのローカルメモリ
// ==========================================
// グローバル変数 g_nodeRssiShort を廃止し、ノードごとの独立したメモリ空間を作成
struct NodeLocalState : public SimpleRefCount<NodeLocalState>
{
    std::map<Mac16Address, int8_t> rssiTable;
};

// シミュレーション評価用のグローバル変数
static std::string g_csvFileName;
static uint32_t g_associatedNodes = 0;
static double g_lastAssociationTime = 0.0;
static uint32_t g_totalTxPackets = 0;

static uint32_t g_positionSamples = 0;
static double g_totalRawPositionError = 0.0;
static double g_totalSomPositionError = 0.0;

static double g_firstAssocScheduleTime = -1.0;
static double g_lastAssocConfirmTime = 0.0;

static std::map<uint32_t, uint32_t> g_nodeRetryCounts;
static const uint32_t MAX_APP_RETRIES = 5;

static bool g_somExecuted[3] = {false, false, false};

// 重複アソシエーションを防ぐための接続完了フラグ
static std::map<uint32_t, bool> g_nodeIsAssociated;

// 各コーディネーターが発行するショートアドレスの現在値（DHCPプール）
static std::map<int, uint16_t> g_coorNextShortAddress;


// ==========================================
// パケット定義・キャッシュ構造体
// ==========================================

struct AnchorInfoMessage 
{
    uint8_t msgType; 
    int anchorId;
    double x;
    double y;
    uint8_t macAddr[2];
};

struct NodeReportMessage 
{
    uint8_t msgType; 
    uint32_t nodeId;
    double x;
    double y;
    int targetAnchorIndex;
};

struct ScheduleCommandMessage 
{
    uint8_t msgType; 
    uint32_t targetNodeId;
    double delayMilliseconds; 
};

struct NodeCacheInfo 
{
    Vector rawPos;
    Mac16Address shortAddr; 
};
static std::map<int, std::map<uint32_t, NodeCacheInfo>> g_coordinatorCaches;

struct AnchorData 
{
    int id;
    Vector pos;
};
static std::map<uint32_t, std::map<Mac16Address, AnchorData>> g_nodeKnownAnchors;

struct NodeContext 
{
    Ptr<LrWpanNetDevice> device;
    MlmeAssociateRequestParams assocParams;
    Vector actualPosition;
    Vector rawPos;
    int anchorId;
    EventId scheduleTimeoutEvent; 
};
static std::map<uint32_t, NodeContext> g_nodeContexts;


// ==========================================
// 補助関数群（計算・カウント）
// ==========================================

static double EstimateDistanceFromRssi(int8_t rssi) 
{
    double rssiAt1m = ENV_TX_POWER - ENV_REF_LOSS;
    double noisyRssi = static_cast<double>(rssi);

    // トンネル坑道特有の対数正規シャドウイング（壁面散乱・人体遮蔽による揺らぎ X_σ）を付加
    if (g_shadowingStdDb > 0.0 && g_rssiNoiseGenerator != nullptr) 
    {
        // NormalRandomVariable::GetValue(平均, 分散 = σ^2)
        double variance = g_shadowingStdDb * g_shadowingStdDb;
        double shadowingNoiseDb = g_rssiNoiseGenerator->GetValue(0.0, variance);
        noisyRssi += shadowingNoiseDb;
    }

    return std::pow(10.0, (rssiAt1m - noisyRssi) / (10.0 * ENV_EXPONENT));
}

static Vector TrilateratePosition(double d1, double d2, double d3) 
{
    double x = (d1 * d1 - d2 * d2 + 2500.0) / 100.0;
    double y = (d1 * d1 - d3 * d3 + 3125.0 - 50.0 * x) / 100.0;
    return Vector(x, y, 0.0);
}

static double Distance2d(const Vector& a, const Vector& b) 
{
    double dx = a.x - b.x;
    double dy = a.y - b.y;
    return std::sqrt(dx * dx + dy * dy);
}

static void MacTxCount(std::string context, Ptr<const Packet> packet) 
{
    g_totalTxPackets++;
}

// 物理層フック：MAC層へ渡る前に生RSSI(dBm)を横取りして記録する
static void RecordPdDataIndication(Ptr<NodeLocalState> state, uint32_t nodeId, Ptr<LrWpanMac> mac, uint32_t psduLength, Ptr<Packet> p, uint8_t lqi, int8_t rssi) 
{
    LrWpanMacHeader hdr; 
    Ptr<Packet> packetCopy = p->Copy();

    if (packetCopy->PeekHeader(hdr)) 
    {
        if (hdr.GetType() == LrWpanMacHeader::LRWPAN_MAC_BEACON && hdr.GetSrcAddrMode() == LrWpanMacHeader::SHORTADDR) 
        {
            // グローバルではなく、個別のメモリ空間にRSSIを保存する
            state->rssiTable[hdr.GetShortSrcAddr()] = rssi;
        }
    }
    mac->PdDataIndication(psduLength, p, lqi, rssi);
}


// ==========================================
// リカバリ・再送制御ロジック
// ==========================================

//再送時にRSSIのクリアを行うため、state を受け取る
static void RetryConnection(Ptr<NodeLocalState> state, Ptr<LrWpanNetDevice> device) 
{
    uint32_t nodeId = device->GetNode()->GetId();
    
    // すでに接続成功済みの場合は再送しない
    if (g_nodeIsAssociated[nodeId])
    {
        return;
    }

    if (g_nodeRetryCounts[nodeId] < MAX_APP_RETRIES) 
    {
        g_nodeRetryCounts[nodeId]++;
        Ptr<UniformRandomVariable> uv = CreateObject<UniformRandomVariable>();
        double backoff = uv->GetValue(1.0, 5.0); 

        std::cout << Simulator::Now().GetSeconds() << "s [Node " << nodeId 
                  << "] App-Layer Retry (Attempt " << g_nodeRetryCounts[nodeId] 
                  << "/" << MAX_APP_RETRIES << ") after " << backoff << "s...\n";

        // メモ帳のRSSI履歴を初期化
        state->rssiTable.clear();

        MlmeScanRequestParams scanParams;
        scanParams.m_chPage = 0; 
        scanParams.m_scanChannels = 0x0800; 
        scanParams.m_scanDuration = 3; 
        scanParams.m_scanType = MLMESCAN_ACTIVE;

        Simulator::ScheduleWithContext(nodeId, Seconds(backoff), &LrWpanMac::MlmeScanRequest, device->GetMac(), scanParams);
    } 
    else 
    {
        std::cout << Simulator::Now().GetSeconds() << "s [Node " << nodeId << "] Max retries reached. Giving up.\n";
    }
}

//RetryConnection に state を渡すため、ここでも受け取る
static void ScheduleCommandTimeout(Ptr<NodeLocalState> state, Ptr<LrWpanNetDevice> device) 
{
    uint32_t nodeId = device->GetNode()->GetId();
    
    if (g_nodeIsAssociated[nodeId]) 
    {
        return;
    }

    std::cout << Simulator::Now().GetSeconds() << "s [Node " << nodeId 
              << "] Schedule Command Timeout! Request/Command packet lost. Retrying...\n";

    RetryConnection(state, device);
}


// ==========================================
// 【Step 1】アンカーからノードへの座標共有
// ==========================================

static void BroadcastAnchorInfo(Ptr<LrWpanNetDevice> coorDevice, int anchorId, Vector pos) 
{
    AnchorInfoMessage msg;
    msg.msgType = 0;
    msg.anchorId = anchorId;
    msg.x = pos.x;
    msg.y = pos.y;
    Mac16Address mac = coorDevice->GetMac()->GetShortAddress();
    uint8_t buffer[2];
    mac.CopyTo(buffer);
    msg.macAddr[0] = buffer[0];
    msg.macAddr[1] = buffer[1];
    
    Ptr<Packet> p = Create<Packet>(reinterpret_cast<const uint8_t*>(&msg), sizeof(AnchorInfoMessage));
    
    McpsDataRequestParams dataParams;
    dataParams.m_dstAddrMode = SHORT_ADDR;
    dataParams.m_dstPanId = 0xFFFF; 
    dataParams.m_dstAddr = Mac16Address("ff:ff");
    dataParams.m_srcAddrMode = SHORT_ADDR;
    dataParams.m_txOptions = 0;
    
    coorDevice->GetMac()->McpsDataRequest(dataParams, p);
}


// ==========================================
// 【パケット受信処理】ノード側・アンカー側
// ==========================================

// ノード側：アンカー情報の学習(Step 1) と、下りスケジュール指示(Step 4)の受信
static void NodeDataIndication(uint32_t nodeId, Ptr<LrWpanNetDevice> device, McpsDataIndicationParams params, Ptr<Packet> p) 
{
    if (g_nodeIsAssociated[nodeId]) 
    {
        return;
    }

    uint8_t msgType;
    p->CopyData(&msgType, 1);
    
    if (msgType == 0 && p->GetSize() >= sizeof(AnchorInfoMessage)) 
    {
        AnchorInfoMessage msg;
        p->CopyData(reinterpret_cast<uint8_t*>(&msg), sizeof(AnchorInfoMessage));
        Mac16Address mac; 
        mac.CopyFrom(msg.macAddr);
        g_nodeKnownAnchors[nodeId][mac] = {msg.anchorId, Vector(msg.x, msg.y, 0)};
        
    } 
    else if (msgType == 2 && p->GetSize() >= sizeof(ScheduleCommandMessage)) 
    {
        ScheduleCommandMessage msg;
        p->CopyData(reinterpret_cast<uint8_t*>(&msg), sizeof(ScheduleCommandMessage));
        
        if (msg.targetNodeId == nodeId) 
        {
            if (g_nodeContexts.find(nodeId) != g_nodeContexts.end()) 
            {
                auto& ctx = g_nodeContexts[nodeId];
                
                Simulator::Cancel(ctx.scheduleTimeoutEvent);

                if (g_firstAssocScheduleTime < 0.0) 
                {
                    g_firstAssocScheduleTime = Simulator::Now().GetSeconds() + (msg.delayMilliseconds / 1000.0);
                }

                std::cout << Simulator::Now().GetSeconds() << "s [Node " << nodeId 
                          << "] Received Schedule Command. Wait " << msg.delayMilliseconds << "ms relative time.\n";

                Simulator::Schedule(MilliSeconds(msg.delayMilliseconds), 
                                     &LrWpanMac::MlmeAssociateRequest, ctx.device->GetMac(), ctx.assocParams);
            }
        }
    }
}

// アンカー側：ノードからのRaw座標報告(Step 3)の受信
static void CoordinatorDataIndication(int anchorId, Ptr<LrWpanNetDevice> coorDevice, McpsDataIndicationParams params, Ptr<Packet> p) 
{
    uint8_t msgType;
    p->CopyData(&msgType, 1);
    
    if (msgType == 1 && p->GetSize() >= sizeof(NodeReportMessage)) 
    {
        NodeReportMessage msg;
        p->CopyData(reinterpret_cast<uint8_t*>(&msg), sizeof(NodeReportMessage));
        
        g_coordinatorCaches[anchorId][msg.nodeId] = { Vector(msg.x, msg.y, 0.0), params.m_srcAddr };
        
        std::cout << Simulator::Now().GetSeconds() << "s [Coordinator " << anchorId 
                  << "] Received Raw Position from Node " << msg.nodeId << "\n";

        // 遅れて再送されてきた座標データに対する、個別の即時スケジュール指示返信
        if (g_somExecuted[anchorId]) 
        {
            Vector anchorPos(0,0,0);
            if (anchorId == 0) 
            {
                anchorPos = Vector(0, 0, 0);
            }
            else if (anchorId == 1) 
            {
                anchorPos = Vector(50, 0, 0);
            }
            else if (anchorId == 2) 
            {
                anchorPos = Vector(25, 50, 0);
            }

            double distance = Distance2d(Vector(msg.x, msg.y, 0.0), anchorPos);
            double delayMs = (0.1 * distance) * 1000.0;

            ScheduleCommandMessage cmd;
            cmd.msgType = 2;
            cmd.targetNodeId = msg.nodeId;
            cmd.delayMilliseconds = delayMs;

            Ptr<Packet> replyP = Create<Packet>(reinterpret_cast<const uint8_t*>(&cmd), sizeof(ScheduleCommandMessage));
            McpsDataRequestParams dataParams;
            dataParams.m_dstAddrMode = SHORT_ADDR;
            dataParams.m_dstPanId = 0xFFFF; 
            dataParams.m_dstAddr = params.m_srcAddr;
            dataParams.m_srcAddrMode = SHORT_ADDR;
            dataParams.m_txOptions = 0;

            coorDevice->GetMac()->McpsDataRequest(dataParams, replyP);
            std::cout << "Coordinator " << anchorId << " -> [RETRY] Dispatching Schedule to Node " 
                      << msg.nodeId << " (Wait: " << delayMs << "ms)\n";
        }
    }
}


// ==========================================
// 【Step 2 & 3】ネットワーク探索と初期測位報告
// ==========================================

// 自分のメモ帳(NodeLocalState)を受け取って計算に使う
static void ScanConfirm(Ptr<NodeLocalState> state, Ptr<LrWpanNetDevice> device, MlmeScanConfirmParams params) 
{
    uint32_t nodeId = device->GetNode()->GetId();
    
    if (g_nodeIsAssociated[nodeId]) 
    {
        return;
    }

    if (params.m_status != MacStatus::SUCCESS || params.m_panDescList.empty()) 
    {
        std::cout << Simulator::Now().GetSeconds() << "s Node " << nodeId << " MLME-scan.confirm: FAILED (No Beacons)\n";
        RetryConnection(state, device);
        return;
    }

    double minDistance = std::numeric_limits<double>::infinity();
    int panDescIndex = -1;

    for (uint32_t i = 0; i < params.m_panDescList.size(); i++)
    {
        SuperframeField superframe(params.m_panDescList[i].m_superframeSpec);
        if (!superframe.IsAssocPermit()) 
        {
            continue;
        }
        if (params.m_panDescList[i].m_coorAddrMode == SHORT_ADDR) 
        {
            auto it = state->rssiTable.find(params.m_panDescList[i].m_coorShortAddr);
            if (it != state->rssiTable.end()) 
            {
                double estimatedDistance = EstimateDistanceFromRssi(it->second);
                if (estimatedDistance < minDistance) 
                {
                    minDistance = estimatedDistance;
                    panDescIndex = i;
                }
            }
        }
    }

    if (panDescIndex < 0) 
    {
        RetryConnection(state, device);
        return;
    }

    std::map<int, double> anchorDistances;
    for (auto const& [mac, rssi] : state->rssiTable) 
    {
        if (g_nodeKnownAnchors[nodeId].find(mac) != g_nodeKnownAnchors[nodeId].end()) 
        {
            int aId = g_nodeKnownAnchors[nodeId][mac].id;
            anchorDistances[aId] = EstimateDistanceFromRssi(rssi);
        }
    }

    if (anchorDistances.count(0) && anchorDistances.count(1) && anchorDistances.count(2)) 
    {
        double d1 = anchorDistances[0];
        double d2 = anchorDistances[1];
        double d3 = anchorDistances[2];
        
        Mac16Address targetMac = params.m_panDescList[panDescIndex].m_coorShortAddr;
        int anchorId = -1;
        if (g_nodeKnownAnchors[nodeId].find(targetMac) != g_nodeKnownAnchors[nodeId].end()) 
        {
            anchorId = g_nodeKnownAnchors[nodeId][targetMac].id;
        }

        if (anchorId == -1) 
        {
            RetryConnection(state, device); 
            return;
        }

        MlmeAssociateRequestParams assocParams;
        assocParams.m_chNum = params.m_panDescList[panDescIndex].m_logCh;
        assocParams.m_chPage = params.m_panDescList[panDescIndex].m_logChPage;
        assocParams.m_coordPanId = params.m_panDescList[panDescIndex].m_coorPanId;
        assocParams.m_coordAddrMode = AddressMode::SHORT_ADDR;
        assocParams.m_coordShortAddr = targetMac;
        CapabilityField capability; 
        capability.SetShortAddrAllocOn(true);
        assocParams.m_capabilityInfo = capability.GetCapability();

        Vector rawPos = TrilateratePosition(d1, d2, d3);
        Ptr<ConstantPositionMobilityModel> actualMobility = device->GetNode()->GetObject<ConstantPositionMobilityModel>();
        Vector actualPosition = actualMobility ? actualMobility->GetPosition() : Vector(0,0,0);

        // タイムアウトスケジュールの引数にも state を引き継ぐ
        EventId timeoutEvent = Simulator::Schedule(Seconds(6.0), &ScheduleCommandTimeout, state, device);
        g_nodeContexts[nodeId] = {device, assocParams, actualPosition, rawPos, anchorId, timeoutEvent};

        NodeReportMessage msg;
        msg.msgType = 1;
        msg.nodeId = nodeId;
        msg.x = rawPos.x;
        msg.y = rawPos.y;
        msg.targetAnchorIndex = anchorId;
        Ptr<Packet> p = Create<Packet>(reinterpret_cast<const uint8_t*>(&msg), sizeof(NodeReportMessage));

        McpsDataRequestParams dataParams;
        dataParams.m_dstAddrMode = SHORT_ADDR;
        dataParams.m_dstPanId = params.m_panDescList[panDescIndex].m_coorPanId;
        dataParams.m_dstAddr = targetMac;
        dataParams.m_srcAddrMode = SHORT_ADDR;
        dataParams.m_txOptions = 0;

        device->GetMac()->McpsDataRequest(dataParams, p);

    } 
    else 
    {
        RetryConnection(state, device);
    }
}


// ==========================================
// 【Step 4】アンカーによるSOM補正とスケジュール指示
// ==========================================

static void CoordinatorExecuteSomAndSchedule(int anchorId, Ptr<LrWpanNetDevice> coorDevice) 
{
    g_somExecuted[anchorId] = true; 

    auto& cache = g_coordinatorCaches[anchorId];
    if (cache.empty()) 
    {
        return;
    }

    std::cout << "\n=== [Coordinator " << anchorId << "] Starting local SOM with " << cache.size() << " nodes ===" << std::endl;

    struct NodeItem 
    {
        uint32_t id;
        Vector raw;
        Vector som;
        Mac16Address shortAddr;
    };
    std::vector<NodeItem> items;
    for (auto const& [nodeId, info] : cache) 
    {
        items.push_back({nodeId, info.rawPos, info.rawPos, info.shortAddr});
    }

    int max_iterations = 20;
    double initial_alpha = 0.4; 
    double neighbor_range = 10.0;
    int num_items = items.size();

    if (num_items > 1) 
    {
        for (int iter = 1; iter <= max_iterations; ++iter) 
        {
            double alpha = initial_alpha * (1.0 - static_cast<double>(iter - 1) / max_iterations);
            std::vector<Vector> next_coords(num_items);

            for (int i = 0; i < num_items; ++i) 
            {
                double sum_x = items[i].som.x;
                double sum_y = items[i].som.y;
                int neighbor_count = 1; 

                for (int j = 0; j < num_items; ++j) 
                {
                    if (i == j) 
                    {
                        continue;
                    }
                    double dist = Distance2d(items[i].som, items[j].som);

                    if (dist < neighbor_range) 
                    {
                        sum_x += items[j].som.x;
                        sum_y += items[j].som.y;
                        neighbor_count++;
                    }
                }

                if (neighbor_count > 1) 
                { 
                    double centroid_x = sum_x / neighbor_count;
                    double centroid_y = sum_y / neighbor_count;
                    double pull_to_raw_x = items[i].raw.x - items[i].som.x;
                    double pull_to_raw_y = items[i].raw.y - items[i].som.y;

                    next_coords[i].x = items[i].som.x + alpha * (centroid_x - items[i].som.x) + (alpha * 0.5) * pull_to_raw_x;
                    next_coords[i].y = items[i].som.y + alpha * (centroid_y - items[i].som.y) + (alpha * 0.5) * pull_to_raw_y;
                    next_coords[i].z = 0.0;
                } 
                else 
                {
                    next_coords[i] = items[i].som;
                }
            }

            for (int i = 0; i < num_items; ++i) 
            {
                items[i].som = next_coords[i];
            }
        }
    }

    Vector anchorPos(0,0,0);
    if (anchorId == 0) 
    {
        anchorPos = Vector(0, 0, 0);
    }
    else if (anchorId == 1) 
    {
        anchorPos = Vector(50, 0, 0);
    }
    else if (anchorId == 2) 
    {
        anchorPos = Vector(25, 50, 0);
    }

    for (auto const& item : items) 
    {
        uint32_t nodeId = item.id;
        if (g_nodeContexts.find(nodeId) == g_nodeContexts.end()) 
        {
            continue;
        }

        auto& ctx = g_nodeContexts[nodeId];
        Vector somCoord = item.som;
        
        double somDistance = Distance2d(somCoord, anchorPos);
        double delayMs = (0.1 * somDistance) * 1000.0;

        ScheduleCommandMessage cmd;
        cmd.msgType = 2;
        cmd.targetNodeId = nodeId;
        cmd.delayMilliseconds = delayMs;

        Ptr<Packet> p = Create<Packet>(reinterpret_cast<const uint8_t*>(&cmd), sizeof(ScheduleCommandMessage));
        
        McpsDataRequestParams dataParams;
        dataParams.m_dstAddrMode = SHORT_ADDR;
        dataParams.m_dstPanId = 0xFFFF; 
        dataParams.m_dstAddr = item.shortAddr;
        dataParams.m_srcAddrMode = SHORT_ADDR;
        dataParams.m_txOptions = 0;

        coorDevice->GetMac()->McpsDataRequest(dataParams, p);
        
        std::cout << "Coordinator " << anchorId << " -> Dispatching Schedule to Node " << nodeId 
                  << " (Wait: " << delayMs << "ms)\n";

        double rawError = Distance2d(ctx.rawPos, ctx.actualPosition);
        double somError = Distance2d(somCoord, ctx.actualPosition);
        g_positionSamples++;
        g_totalRawPositionError += rawError;
        g_totalSomPositionError += somError;

        std::ofstream csvFile(g_csvFileName, std::ios::app);
        csvFile << nodeId << "," << ctx.actualPosition.x << "," << ctx.actualPosition.y << "," 
                << ctx.rawPos.x << "," << ctx.rawPos.y << "," << somCoord.x << "," << somCoord.y << "," 
                << (anchorId + 1) << "\n";
        csvFile.close();
    }
}


// ==========================================
// 【Step 5】アソシエーション（接続実行と確認）
// ==========================================

// 【引数追加】どのアンカーが呼ばれたか判別するため anchorId を受け取る
static void AssociateIndication(int anchorId, Ptr<LrWpanNetDevice> device, MlmeAssociateIndicationParams params) 
{
    MlmeAssociateResponseParams assocRespParams;
    assocRespParams.m_extDevAddr = params.m_extDevAddr;
    assocRespParams.m_status = MacStatus::SUCCESS;
    
    // アドレスプールの初期化（最初の1回だけ実行）
    if (g_coorNextShortAddress.find(anchorId) == g_coorNextShortAddress.end()) 
    {
        // アンカー0は0x1001～, アンカー1は0x2001～, アンカー2は0x3001～ という規則で開始値を設定
        g_coorNextShortAddress[anchorId] = ((anchorId + 1) << 12) | 0x0001; 
    }

    // 次のショートアドレスを割り当てて、プールの現在値を1進める
    uint16_t allocatedAddr = g_coorNextShortAddress[anchorId]++;
    
    uint8_t buffer16MacAddr[2];
    buffer16MacAddr[0] = (allocatedAddr >> 8) & 0xFF; // 上位バイト (例: 0x10)
    buffer16MacAddr[1] = allocatedAddr & 0xFF;        // 下位バイト (例: 0x01)
    
    Mac16Address shortAddr; 
    shortAddr.CopyFrom(buffer16MacAddr);
    assocRespParams.m_assocShortAddr = shortAddr;

    Simulator::ScheduleNow(&LrWpanMac::MlmeAssociateResponse, device->GetMac(), assocRespParams);
}

//再送処理へつなぐ可能性があるため state を受け取る
static void AssociateConfirm(Ptr<NodeLocalState> state, Ptr<LrWpanNetDevice> device, MlmeAssociateConfirmParams params) 
{
    uint32_t nodeId = device->GetNode()->GetId();
    double currentTime = Simulator::Now().GetSeconds();

    if (params.m_status == MacStatus::SUCCESS) 
    {
        if (g_nodeIsAssociated[nodeId]) 
        {
            return;
        }

        g_nodeIsAssociated[nodeId] = true; 
        g_associatedNodes++;

        if (currentTime > g_lastAssociationTime) 
        { 
            g_lastAssociationTime = currentTime; 
        }
        g_lastAssocConfirmTime = currentTime;
        std::cout << currentTime << "s Node " << nodeId << " MLME-assoc: SUCCESS\n";
    } 
    else 
    {
        std::cout << currentTime << "s Node " << nodeId 
                  << " MLME-assoc: FAILED (Status: " << params.m_status << ")\n";
        RetryConnection(state, device);
    }
}


// ==========================================
// シミュレーション結果出力およびメイン関数
// ==========================================

static void PrintSimulationResults(uint32_t totalNodes) 
{
    std::cout << "\n=== COORDINATOR-AGGREGATED SOM METHOD SUMMARY ===\n";
    std::cout << "Attempted: " << totalNodes << " | Success: " << g_associatedNodes << " (" << (g_associatedNodes * 100.0 / totalNodes) << "%)\n";
    std::cout << "Completion Time: " << g_lastAssociationTime << "s | Total Packets: " << g_totalTxPackets << "\n";
    
    if (g_firstAssocScheduleTime >= 0.0 && g_lastAssocConfirmTime >= g_firstAssocScheduleTime) 
    {
        double totalProcessSpan = g_lastAssocConfirmTime - g_firstAssocScheduleTime;
        std::cout << "Total Association Process Span (First Request Schedule -> Last Confirm Success): " << totalProcessSpan << "s\n";
    }

    if (g_positionSamples > 0) 
    {
        std::cout << "Average Raw Position Error: " << (g_totalRawPositionError / g_positionSamples) << "m\n";
        std::cout << "Average SOM Position Error: " << (g_totalSomPositionError / g_positionSamples) << "m\n";
    }
}

int main(int argc, char* argv[]) 
{
    uint32_t numNodes = 10;
    CommandLine cmd(__FILE__);
    cmd.AddValue("numNodes", "Number of nodes", numNodes);
    cmd.AddValue("sigma", "Shadowing standard deviation in dB (tunnel noise)", g_shadowingStdDb);
    cmd.Parse(argc, argv);

    std::string nodeStr = std::to_string(numNodes) + "Node";
    g_csvFileName = "CoordinatorSOM_position_results_" + nodeStr + ".csv";
    std::string pcapPrefix = "CoordinatorSOM-lr-wpan-" + nodeStr;

    RngSeedManager::SetSeed(5); 
    RngSeedManager::SetRun(4);

    // SeedとRunの設定後に乱数生成器を初期化する（反復試行の再現性確保）
    g_rssiNoiseGenerator = CreateObject<NormalRandomVariable>();

    Config::SetDefault("ns3::LogDistancePropagationLossModel::ReferenceLoss", DoubleValue(ENV_REF_LOSS));
    Config::SetDefault("ns3::LogDistancePropagationLossModel::Exponent", DoubleValue(ENV_EXPONENT));
    GlobalValue::Bind("ChecksumEnabled", BooleanValue(true));

    nodes.Create(numNodes); 
    coordinators.Create(3);
    const Vector coordA(0, 0, 0); 
    const Vector coordB(50, 0, 0); 
    const Vector coordC(25, 50, 0);
    Vector coordPos[3] = {coordA, coordB, coordC};

    std::ofstream csvFileInit(g_csvFileName);
    csvFileInit << "NodeID,ActualX,ActualY,RawEstimatedX,RawEstimatedY,SomEstimatedX,SomEstimatedY,AnchorID\n";
    csvFileInit.close();

    Ptr<ListPositionAllocator> coordAlloc = CreateObject<ListPositionAllocator>();
    coordAlloc->Add(coordA); 
    coordAlloc->Add(coordB); 
    coordAlloc->Add(coordC);
    MobilityHelper coordMobility;
    coordMobility.SetMobilityModel("ns3::ConstantPositionMobilityModel");
    coordMobility.SetPositionAllocator(coordAlloc);
    coordMobility.Install(coordinators);

    //Seedの値によってノードの位置が変わるように、UniformRandomVariableを使って三角形内にランダム配置
    Ptr<UniformRandomVariable> uv = CreateObject<UniformRandomVariable>();
    auto RandomPointInTriangle = [&](const Vector& a, const Vector& b, const Vector& c) 
    {
        double u = uv->GetValue(0.0, 1.0);
        double v = uv->GetValue(0.0, 1.0);
        if (u + v > 1.0) 
        { 
            u = 1.0 - u; 
            v = 1.0 - v; 
        }
        return Vector(a.x + u * (b.x - a.x) + v * (c.x - a.x), a.y + u * (b.y - a.y) + v * (c.y - a.y), 0);
    };

    Ptr<ListPositionAllocator> nodePosAlloc = CreateObject<ListPositionAllocator>();
    for (uint32_t i = 0; i < nodes.GetN(); ++i) 
    {
        nodePosAlloc->Add(RandomPointInTriangle(coordA, coordB, coordC)); 
    }

    MobilityHelper nodeMobility;
    nodeMobility.SetMobilityModel("ns3::ConstantPositionMobilityModel");
    nodeMobility.SetPositionAllocator(nodePosAlloc);
    nodeMobility.Install(nodes);

    LrWpanHelper lrWpanHelper;
    lrWpanHelper.SetPropagationDelayModel("ns3::ConstantSpeedPropagationDelayModel");
    lrWpanHelper.AddPropagationLossModel("ns3::LogDistancePropagationLossModel");

    NetDeviceContainer lrwpanDevices = lrWpanHelper.Install(nodes);
    lrwpanDevices.Add(lrWpanHelper.Install(coordinators));

    lrWpanHelper.EnablePcapAll(pcapPrefix, true);
    Config::Connect("/NodeList/*/DeviceList/*/Mac/MacTx", MakeCallback(&MacTxCount));

    for (uint32_t i = 0; i < nodes.GetN(); ++i) 
    {
        Ptr<LrWpanNetDevice> nodeDevice = DynamicCast<LrWpanNetDevice>(nodes.Get(i)->GetDevice(0));
        uint32_t nodeId = nodes.Get(i)->GetId();

        // 【追加】ノードごとに独立したローカルメモリ空間（メモ帳）を生成
        Ptr<NodeLocalState> localState = Create<NodeLocalState>();

        g_nodeIsAssociated[nodeId] = false;
        g_nodeRetryCounts[nodeId] = 0; 

        Mac64Address extAddr;
        uint8_t addrBuffer[8] = {0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, static_cast<uint8_t>(i + 1)};
        extAddr.CopyFrom(addrBuffer);
        nodeDevice->GetMac()->SetExtendedAddress(extAddr);
        // 実機環境の仕様に準拠するため、ノードへのショートアドレスの事前付与を廃止

        // 【修正】各コールバック関数に、ノード固有の「メモ帳(localState)」を紐付けて（バインドして）渡す
        nodeDevice->GetMac()->SetMlmeScanConfirmCallback(MakeBoundCallback(&ScanConfirm, localState, nodeDevice));
        nodeDevice->GetMac()->SetMlmeAssociateConfirmCallback(MakeBoundCallback(&AssociateConfirm, localState, nodeDevice));
        nodeDevice->GetPhy()->SetPdDataIndicationCallback(MakeBoundCallback(&RecordPdDataIndication, localState, nodeId, nodeDevice->GetMac()));
        nodeDevice->GetMac()->SetMcpsDataIndicationCallback(MakeBoundCallback(&NodeDataIndication, nodeId, nodeDevice));
     
        MlmeScanRequestParams scanParams;
        scanParams.m_chPage = 0; 
        scanParams.m_scanChannels = 0x0800; 
        scanParams.m_scanDuration = 3; 
        scanParams.m_scanType = MLMESCAN_ACTIVE;
        
        Simulator::ScheduleWithContext(nodeId, Seconds(3) + MilliSeconds(i * 50), &LrWpanMac::MlmeScanRequest, nodeDevice->GetMac(), scanParams);
    }
    
    for (uint32_t i = 0; i < coordinators.GetN(); ++i) 
    {
        Ptr<LrWpanNetDevice> coorDevice = DynamicCast<LrWpanNetDevice>(coordinators.Get(i)->GetDevice(0));
        coorDevice->GetMac()->SetMlmeAssociateIndicationCallback(MakeBoundCallback(&AssociateIndication, i, coorDevice));
        coorDevice->GetMac()->SetMcpsDataIndicationCallback(MakeBoundCallback(&CoordinatorDataIndication, i, coorDevice));

        uint8_t id = i + 1;
        uint8_t addrBufferC[8] = {0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, static_cast<uint8_t>(id)};
        Mac64Address extAddrC; extAddrC.CopyFrom(addrBufferC);
        std::string sId = std::to_string(id);
        std::string shortAddrStr = sId + sId + ":" + sId + sId;
        
        coorDevice->GetMac()->SetExtendedAddress(extAddrC);
        coorDevice->GetMac()->SetShortAddress(Mac16Address(shortAddrStr.c_str()));

        MlmeStartRequestParams params;
        params.m_panCoor = true; 
        params.m_PanId = 0x0005;
        params.m_bcnOrd = 15; 
        params.m_sfrmOrd = 15; 
        params.m_logCh = 11; 
        Simulator::ScheduleWithContext(coorDevice->GetNode()->GetId(), Seconds(2), &LrWpanMac::MlmeStartRequest, coorDevice->GetMac(), params);
        coorDevice->GetMac()->m_macAssociationPermit = true;

        Simulator::ScheduleWithContext(coorDevice->GetNode()->GetId(), Seconds(2.5) + MilliSeconds(i * 50), &BroadcastAnchorInfo, coorDevice, i, coordPos[i]);
        Simulator::ScheduleWithContext(coorDevice->GetNode()->GetId(), Seconds(8.1) + MilliSeconds(i * 100), &CoordinatorExecuteSomAndSchedule, i, coorDevice);
    }

    Simulator::Schedule(Seconds(24.9), &PrintSimulationResults, numNodes);

    Simulator::Stop(Seconds(25));
    Simulator::Run();
    Simulator::Destroy();
    return 0;
}