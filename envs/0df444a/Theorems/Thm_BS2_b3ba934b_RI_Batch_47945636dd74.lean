-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_47945636dd74
-- name    : BS2_b3ba934b_RI_Batch_47945636dd74
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:39:26.317981+00:00
-- url     : https://prove2.me/theorems/fd76259a-3844-4224-8978-ec6cda20a4c1
-- title:
--   Sensitivity record certificate: Batch_47945636dd74
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type6_27_chunk1024, checked_type6_27_chunk1088, checked_type6_27_chunk1152, checked_type6_27_chunk1216, checked_type6_27_chunk1280, checked_type6_27_chunk1344, checked_type6_27_chunk1408, checked_type6_27_chunk1472, checked_type6_27_chunk768, checked_type6_27_chunk832, checked_type6_27_chunk896, checked_type6_27_chunk960. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks054.lean; original SHA-256 b897186021bb8fa3bb7d5551ac1b6bdfe6a6307f8fde91316a290295d8cf5217; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_47945636dd74 : (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1024 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1088 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1152 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1216 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1280 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1344 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1408 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1472 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 768 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 832 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 896 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 960 64=true) ∧ True := by sorry
