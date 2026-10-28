-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_21c21ff71095
-- name    : BS2_b3ba934b_RI_Batch_21c21ff71095
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:32:12.255199+00:00
-- url     : https://prove2.me/theorems/acde116e-3bfd-4665-9d7a-cd07543e40ae
-- title:
--   Sensitivity record certificate: Batch_21c21ff71095
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type5_136, checked_type5_138, checked_type5_140. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks034.lean; original SHA-256 ab26f7d23e97e14a8a719d6b3b55cc8a7cdad39571ba0fc41fe7df8a956b8f48; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_21c21ff71095 : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,5,5,6,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,5,6,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,7,7,7,7]=true) ∧ True := by sorry
