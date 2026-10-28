-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_105f47f95a02
-- name    : BS2_b3ba934b_RI_Batch_105f47f95a02
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:39:06.616512+00:00
-- url     : https://prove2.me/theorems/2c11290c-ea33-46c8-becc-9bcef84286de
-- title:
--   Sensitivity record certificate: Batch_105f47f95a02
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type6_27_chunk0, checked_type6_27_chunk128, checked_type6_27_chunk192, checked_type6_27_chunk256, checked_type6_27_chunk320, checked_type6_27_chunk384, checked_type6_27_chunk448, checked_type6_27_chunk512, checked_type6_27_chunk576, checked_type6_27_chunk64, checked_type6_27_chunk640, checked_type6_27_chunk704. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks053.lean; original SHA-256 78001f20b9146162220e126b15baaa4de03220d451f088ae1fe72ce04bb8e033; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_105f47f95a02 : (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 0 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 128 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 192 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 256 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 320 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 384 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 448 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 512 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 576 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 64 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 640 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 704 64=true) ∧ True := by sorry
