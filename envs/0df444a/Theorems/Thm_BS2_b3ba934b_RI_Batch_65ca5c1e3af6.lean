-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_65ca5c1e3af6
-- name    : BS2_b3ba934b_RI_Batch_65ca5c1e3af6
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:39:27.158817+00:00
-- url     : https://prove2.me/theorems/2a3fb2dc-a566-4212-9d9d-17b8fe4a4752
-- title:
--   Sensitivity record certificate: Batch_65ca5c1e3af6
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type6_27_chunk2304, checked_type6_27_chunk2368, checked_type6_27_chunk2432, checked_type6_27_chunk2496, checked_type6_27_chunk2560, checked_type6_27_chunk2624, checked_type6_27_chunk2688, checked_type6_27_chunk2752, checked_type6_27_chunk2816, checked_type6_27_chunk2880, checked_type6_27_chunk2944, checked_type6_27_chunk3008. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks056.lean; original SHA-256 08f2ff8c67cc43fe558d2b619fb5dfc1f6516c8e0e1d5a60f12c59043b1827b5; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_65ca5c1e3af6 : (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2304 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2368 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2432 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2496 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2560 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2624 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2688 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2752 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2816 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2880 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2944 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3008 64=true) ∧ True := by sorry
