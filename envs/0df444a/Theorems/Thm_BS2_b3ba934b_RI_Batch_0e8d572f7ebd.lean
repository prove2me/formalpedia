-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_0e8d572f7ebd
-- name    : BS2_b3ba934b_RI_Batch_0e8d572f7ebd
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:19:59.904893+00:00
-- url     : https://prove2.me/theorems/a3abd9a6-d297-40f0-8de5-11323f79f192
-- title:
--   Sensitivity record certificate: Batch_0e8d572f7ebd
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type5_30, checked_type5_31, checked_type5_32, checked_type5_33, checked_type5_34, checked_type5_36, checked_type5_37, checked_type5_38. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks019.lean; original SHA-256 568a7f4210994b8a002c2d51fa129fb82308b8ec24cdba4983f10fbd9931eb6a; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_0e8d572f7ebd : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,3,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,3,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,4,4,4,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,4,4,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,4,4,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,4,5,5,6]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,4,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,4,5,7,7]=true) ∧ True := by sorry
