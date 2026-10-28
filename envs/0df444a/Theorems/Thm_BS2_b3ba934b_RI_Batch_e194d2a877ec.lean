-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_e194d2a877ec
-- name    : BS2_b3ba934b_RI_Batch_e194d2a877ec
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:39:24.746019+00:00
-- url     : https://prove2.me/theorems/5914532a-ae44-4bdc-b010-5c7be3f4cfe5
-- title:
--   Sensitivity record certificate: Batch_e194d2a877ec
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type5_127, checked_type5_129, checked_type5_131. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks032.lean; original SHA-256 78e7d34a038e83e478891734ec975a63b3eb68d3303209a4e8b1ff6a49efe09d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_e194d2a877ec : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,4,5,5,6]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,4,5,6,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,4,7,7,7]=true) ∧ True := by sorry
