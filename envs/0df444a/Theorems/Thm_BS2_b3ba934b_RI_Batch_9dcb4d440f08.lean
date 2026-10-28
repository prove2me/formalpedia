-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_9dcb4d440f08
-- name    : BS2_b3ba934b_RI_Batch_9dcb4d440f08
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:27:27.790423+00:00
-- url     : https://prove2.me/theorems/a4f119f2-0333-4461-b4b0-e5d3d2e7c5e3
-- title:
--   Sensitivity record certificate: Batch_9dcb4d440f08
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type5_123, checked_type5_125. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks031.lean; original SHA-256 45559b0df751a06bad635ec33d691d5fda840647d3b8d7b4c36975e7277f0d7b; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_9dcb4d440f08 : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,4,4,5,6]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,4,4,7,7]=true) ∧ True := by sorry
