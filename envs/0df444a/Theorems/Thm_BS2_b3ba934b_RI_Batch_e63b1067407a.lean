-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_e63b1067407a
-- name    : BS2_b3ba934b_RI_Batch_e63b1067407a
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:32:08.58106+00:00
-- url     : https://prove2.me/theorems/8ff49351-c19b-4d2c-b53a-e5cc898263fe
-- title:
--   Sensitivity record certificate: Batch_e63b1067407a
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type5_144. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks036.lean; original SHA-256 dc1ceca6ce3d92e8de4a12ec88a19728aacf74753b03eb85bc24dee2d8be5932; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_e63b1067407a : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [5,5,5,6,6]=true) ∧ True := by sorry
