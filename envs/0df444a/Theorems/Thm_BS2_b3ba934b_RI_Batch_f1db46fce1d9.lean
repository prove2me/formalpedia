-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_f1db46fce1d9
-- name    : BS2_b3ba934b_RI_Batch_f1db46fce1d9
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:27:19.445675+00:00
-- url     : https://prove2.me/theorems/1ae7ecee-b25d-4808-ae2f-9371932b6090
-- title:
--   Sensitivity record certificate: Batch_f1db46fce1d9
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type5_103, checked_type5_104, checked_type5_105, checked_type5_106, checked_type5_107, checked_type5_108, checked_type5_110, checked_type5_111, checked_type5_112. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks029.lean; original SHA-256 d1175295657d2d1e4793f32b30dab57564730fa4e8b2fd131653355ba8ee2a1a; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_f1db46fce1d9 : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,3,4,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,3,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,3,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,4,4,4,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,4,4,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,4,4,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,4,5,5,6]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,4,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,4,5,7,7]=true) ∧ True := by sorry
