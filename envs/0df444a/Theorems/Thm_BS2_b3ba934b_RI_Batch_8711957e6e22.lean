-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_8711957e6e22
-- name    : BS2_b3ba934b_RI_Batch_8711957e6e22
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:39:25.037636+00:00
-- url     : https://prove2.me/theorems/dcce5423-dd72-4738-83e5-d3a86e547939
-- title:
--   Sensitivity record certificate: Batch_8711957e6e22
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type6_27_chunk3072, checked_type6_27_chunk3136, checked_type6_27_chunk3200, checked_type6_27_chunk3264, checked_type6_27_chunk3328, checked_type6_27_chunk3392, checked_type6_27_chunk3456, checked_type6_27_chunk3520, checked_type6_27_chunk3584, checked_type6_27_chunk3648, checked_type6_27_chunk3712, checked_type6_27_chunk3776. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks057.lean; original SHA-256 4ef00303ea03cf7c272fd661a9d984e9ab082bc48f69c8ab43acd2582401142a; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_8711957e6e22 : (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3072 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3136 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3200 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3264 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3328 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3392 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3456 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3520 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3584 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3648 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3712 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3776 64=true) ∧ True := by sorry
