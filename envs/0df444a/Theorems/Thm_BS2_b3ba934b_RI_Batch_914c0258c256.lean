-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_914c0258c256
-- name    : BS2_b3ba934b_RI_Batch_914c0258c256
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:14:55.304429+00:00
-- url     : https://prove2.me/theorems/527c5cff-596e-4238-96e8-94a9ed96ba3e
-- title:
--   Sensitivity record certificate: Batch_914c0258c256
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type6_0. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks037.lean; original SHA-256 89df839c71b21b0380d88584df0a9cf167fa03529898e2e470242a565878444d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_914c0258c256 : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [0,5,5,5,5,5]=true) ∧ True := by sorry
