-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_0997866a336d
-- name    : BS2_b3ba934b_RI_Batch_0997866a336d
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:32:18.013393+00:00
-- url     : https://prove2.me/theorems/1f3d0fcd-e7b9-49d5-8e6c-729ef0dee1dc
-- title:
--   Sensitivity record certificate: Batch_0997866a336d
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type6_10, checked_type6_11, checked_type6_12, checked_type6_13, checked_type6_14, checked_type6_15, checked_type6_16, checked_type6_17. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble07.lean; original SHA-256 56a7e8d2ecc356dc463e91065c393df4856408ba3e64f4f651679cf659f63803; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_0997866a336d : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,4,4,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,4,5,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,4,5,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,5,5,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,5,5,5,5,6]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,5,5,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,5,5,5,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,4,5,5,5,5]=true) ∧ True := by sorry
