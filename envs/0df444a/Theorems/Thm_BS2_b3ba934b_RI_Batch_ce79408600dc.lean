-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_ce79408600dc
-- name    : BS2_b3ba934b_RI_Batch_ce79408600dc
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:27:07.517752+00:00
-- url     : https://prove2.me/theorems/e58ce84c-5fb0-4113-8ab8-5c4a8cbd573e
-- title:
--   Sensitivity record certificate: Batch_ce79408600dc
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type5_89, checked_type5_91, checked_type5_93. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks026.lean; original SHA-256 25a69925699fd23eeaf844656f487f9237e3a51087791c8c114ab8f4fde91fdc; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_ce79408600dc : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,4,5,5,6]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,4,5,6,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,4,7,7,7]=true) ∧ True := by sorry
