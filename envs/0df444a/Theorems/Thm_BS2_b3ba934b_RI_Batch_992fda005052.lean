-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_992fda005052
-- name    : BS2_b3ba934b_RI_Batch_992fda005052
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:19:54.198949+00:00
-- url     : https://prove2.me/theorems/11af31a6-2aac-47c8-a0b3-e9531cd53e9d
-- title:
--   Sensitivity record certificate: Batch_992fda005052
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type5_19, checked_type5_20, checked_type5_21, checked_type5_22, checked_type5_23, checked_type5_24, checked_type5_26, checked_type5_27, checked_type5_28, checked_type5_29. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks018.lean; original SHA-256 3e4364544df618c519a4735850945dfcfa7f6c90aecc574ddef12143b9fc3ce7; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_992fda005052 : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,2,2,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,2,2,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,2,3,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,2,4,4,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,2,4,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,2,4,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,2,5,5,6]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,2,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,2,5,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,3,4,5,5]=true) ∧ True := by sorry
