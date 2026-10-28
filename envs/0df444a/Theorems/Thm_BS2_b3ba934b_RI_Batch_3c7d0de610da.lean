-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_3c7d0de610da
-- name    : BS2_b3ba934b_RI_Batch_3c7d0de610da
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:20:05.516845+00:00
-- url     : https://prove2.me/theorems/e3a6c3b1-d836-45d6-91af-b0f0b302c74e
-- title:
--   Sensitivity record certificate: Batch_3c7d0de610da
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type5_25, checked_type5_35, checked_type5_39, checked_type5_41, checked_type5_47, checked_type5_51, checked_type5_53, checked_type5_55. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble00.lean; original SHA-256 8ad8b7774194d31c0d8254ab3b0eccaac588a4b9c4d316499dba757b31d730fa; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_3c7d0de610da : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,2,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,4,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,5,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,5,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,2,2,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,2,4,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,2,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,2,5,7]=true) ∧ True := by sorry
