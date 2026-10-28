-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_70ccdec8ec3e
-- name    : BS2_b3ba934b_RI_Batch_70ccdec8ec3e
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:27:12.212171+00:00
-- url     : https://prove2.me/theorems/0961feb7-0da3-41de-8551-e375b2c4217f
-- title:
--   Sensitivity record certificate: Batch_70ccdec8ec3e
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type5_101, checked_type5_109, checked_type5_113, checked_type5_115, checked_type5_120, checked_type5_122, checked_type5_124, checked_type5_99. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble03.lean; original SHA-256 e648acb18b5ef5f0b45d2c61d5f4b056fb0e824af70f1f2e5a6505c3dab2064f; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_70ccdec8ec3e : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,5,7,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,4,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,5,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,5,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,4,4,4,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,4,4,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,4,4,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,5,5,7,7]=true) ∧ True := by sorry
