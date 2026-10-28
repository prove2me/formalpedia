-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_04e2a8d7543d
-- name    : BS2_b3ba934b_RI_Batch_04e2a8d7543d
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:34:06.472984+00:00
-- url     : https://prove2.me/theorems/777f20dd-68d8-4bbc-879f-edbca5abb145
-- title:
--   Sensitivity record certificate: Batch_04e2a8d7543d
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type6_31_chunk512, checked_type6_31_chunk576, checked_type6_31_chunk640, checked_type6_32_chunk0, checked_type6_32_chunk128, checked_type6_32_chunk64. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks064.lean; original SHA-256 af4888cab7be3d17744ecadcb96b5a6470afbe5f9abba574ec7513eae24d45f0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_04e2a8d7543d : (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,7,7] 512 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,7,7] 576 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,7,7] 640 48=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,7,7,7] 0 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,7,7,7] 128 4=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,7,7,7] 64 64=true) ∧ True := by sorry
