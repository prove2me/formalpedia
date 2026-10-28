-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_020c9523dfd0
-- name    : BS2_b3ba934b_RI_Batch_020c9523dfd0
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:32:19.149074+00:00
-- url     : https://prove2.me/theorems/914dbaf3-b8a8-40ff-968c-efcdcf7066f1
-- title:
--   Sensitivity record certificate: Batch_020c9523dfd0
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type6_29_chunk1024, checked_type6_29_chunk1088, checked_type6_29_chunk1152, checked_type6_29_chunk1216, checked_type6_29_chunk512, checked_type6_29_chunk576, checked_type6_29_chunk640, checked_type6_29_chunk704, checked_type6_29_chunk768, checked_type6_29_chunk832, checked_type6_29_chunk896, checked_type6_29_chunk960. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks061.lean; original SHA-256 017eae860f09cf845414c33993e577336eef73420e3217b9db15513920ac9111; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_020c9523dfd0 : (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1024 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1088 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1152 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1216 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 512 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 576 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 640 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 704 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 768 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 832 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 896 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 960 64=true) ∧ True := by sorry
