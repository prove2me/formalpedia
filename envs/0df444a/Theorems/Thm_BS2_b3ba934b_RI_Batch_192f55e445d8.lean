-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_192f55e445d8
-- name    : BS2_b3ba934b_RI_Batch_192f55e445d8
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:27:00.238832+00:00
-- url     : https://prove2.me/theorems/eb3328ba-4862-43ee-b232-9d6008fc0670
-- title:
--   Sensitivity record certificate: Batch_192f55e445d8
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type5_81, checked_type5_83, checked_type5_85, checked_type5_87. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks025.lean; original SHA-256 c511ac87460fd9e9560687aca67fe009531af352ad8b49d41a8e9804612c933c; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_192f55e445d8 : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,4,4,4,4]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,4,4,4,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,4,4,5,6]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,4,4,7,7]=true) ∧ True := by sorry
