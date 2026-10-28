-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_c0d235b91e7d
-- name    : BS2_b3ba934b_RI_Batch_c0d235b91e7d
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:32:21.267744+00:00
-- url     : https://prove2.me/theorems/d40605b2-3a2f-4659-a21f-4b14363e4f68
-- title:
--   Sensitivity record certificate: Batch_c0d235b91e7d
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type6_28_chunk192, checked_type6_28_chunk256, checked_type6_28_chunk320, checked_type6_28_chunk384, checked_type6_29_chunk0, checked_type6_29_chunk128, checked_type6_29_chunk192, checked_type6_29_chunk256, checked_type6_29_chunk320, checked_type6_29_chunk384, checked_type6_29_chunk448, checked_type6_29_chunk64. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks060.lean; original SHA-256 3273da7321b6e5a43202c13731f70b8e4f808f71eb241882e8a1192fa622916c; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_c0d235b91e7d : (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] 192 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] 256 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] 320 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] 384 40=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 0 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 128 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 192 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 256 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 320 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 384 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 448 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 64 64=true) ∧ True := by sorry
