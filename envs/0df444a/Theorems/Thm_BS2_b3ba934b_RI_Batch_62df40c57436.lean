-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_62df40c57436
-- name    : BS2_b3ba934b_RI_Batch_62df40c57436
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:18:43.6617+00:00
-- url     : https://prove2.me/theorems/e4fd5729-9dc1-4414-b3d1-c6db1054a890
-- title:
--   Sensitivity record certificate: Batch_62df40c57436
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type5_0, checked_type5_1, checked_type5_2, checked_type5_3, checked_type5_4, checked_type5_5, checked_type5_6. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks016.lean; original SHA-256 f81cf451701f8038f9dff971cf118b6fb9bc658cd290aa667e1862d353a05d4b; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_62df40c57436 : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [0,1,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [0,2,2,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [0,2,4,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [0,2,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [0,2,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [0,3,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [0,4,4,5,5]=true) ∧ True := by sorry
