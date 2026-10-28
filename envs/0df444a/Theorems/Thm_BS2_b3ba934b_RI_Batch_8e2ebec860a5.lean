-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_8e2ebec860a5
-- name    : BS2_b3ba934b_RI_Batch_8e2ebec860a5
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:32:17.561818+00:00
-- url     : https://prove2.me/theorems/f77c37f8-aaed-431b-af18-c1ead354236d
-- title:
--   Sensitivity record certificate: Batch_8e2ebec860a5
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type6_18, checked_type6_19, checked_type6_20, checked_type6_21, checked_type6_22, checked_type6_23, checked_type6_24, checked_type6_25. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble08.lean; original SHA-256 7b427f2f1ab4226192df11dcba7a013ba7724c8dfd09259eb5a4c74e1280d8b6; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_8e2ebec860a5 : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,5,5,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,5,5,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,4,4,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,4,5,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,4,5,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,5,5,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,5,5,5,5,6]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,5,5,5,5,7]=true) ∧ True := by sorry
