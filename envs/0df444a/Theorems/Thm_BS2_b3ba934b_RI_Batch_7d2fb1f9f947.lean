-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_7d2fb1f9f947
-- name    : BS2_b3ba934b_RI_Batch_7d2fb1f9f947
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:27:14.907816+00:00
-- url     : https://prove2.me/theorems/dca09cf5-b039-46be-a8d9-929e1d0c7add
-- title:
--   Sensitivity record certificate: Batch_7d2fb1f9f947
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type5_100, checked_type5_102, checked_type5_97, checked_type5_98. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks028.lean; original SHA-256 f55964cb94964af2b97d33f3edde7131fa3a056364bbb940649c3bf01fef6fdb; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_7d2fb1f9f947 : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,5,6,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,7,7,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,5,5,6,6]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,5,5,6,7]=true) ∧ True := by sorry
