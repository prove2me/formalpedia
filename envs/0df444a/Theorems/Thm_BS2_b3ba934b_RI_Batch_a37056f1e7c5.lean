-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_a37056f1e7c5
-- name    : BS2_b3ba934b_RI_Batch_a37056f1e7c5
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:39:24.451041+00:00
-- url     : https://prove2.me/theorems/930cf36f-ae95-4246-9063-e61e65b8ce19
-- title:
--   Sensitivity record certificate: Batch_a37056f1e7c5
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type6_27_chunk1536, checked_type6_27_chunk1600, checked_type6_27_chunk1664, checked_type6_27_chunk1728, checked_type6_27_chunk1792, checked_type6_27_chunk1856, checked_type6_27_chunk1920, checked_type6_27_chunk1984, checked_type6_27_chunk2048, checked_type6_27_chunk2112, checked_type6_27_chunk2176, checked_type6_27_chunk2240. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks055.lean; original SHA-256 4f6b6754bece55ebd081b2f05fe3deda2dbfa9b019ea82958a558faabc7cd0fc; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_a37056f1e7c5 : (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1536 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1600 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1664 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1728 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1792 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1856 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1920 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1984 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2048 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2112 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2176 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2240 64=true) ∧ True := by sorry
