-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_747a268f3ca9
-- name    : BS2_b3ba934b_RI_Batch_747a268f3ca9
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:27:22.168659+00:00
-- url     : https://prove2.me/theorems/30496311-7798-422d-a9ab-940062b0aac6
-- title:
--   Sensitivity record certificate: Batch_747a268f3ca9
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type5_114, checked_type5_116, checked_type5_117, checked_type5_118, checked_type5_119, checked_type5_121. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks030.lean; original SHA-256 a75aa78ef31f612b3e7f0c688acbc4fb1e190a20834cc73306ef64788d8aab43; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_747a268f3ca9 : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,5,5,5,6]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,5,5,6,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,5,5,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,5,7,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,4,4,4,4]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,4,4,4,7]=true) ∧ True := by sorry
