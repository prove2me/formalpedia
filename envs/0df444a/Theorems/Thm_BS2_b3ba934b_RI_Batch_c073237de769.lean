-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_c073237de769
-- name    : BS2_b3ba934b_RI_Batch_c073237de769
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:26:54.273538+00:00
-- url     : https://prove2.me/theorems/c3b7c789-25c6-4d2e-b217-cdeec02c4a1e
-- title:
--   Sensitivity record certificate: Batch_c073237de769
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type5_66, checked_type5_68, checked_type5_70. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks023.lean; original SHA-256 f6dcbb906b15e26c42e93367e27327e4468a3691a8567e26e429180ebc10b1a0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_c073237de769 : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,4,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,5,5,6]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,5,6,7]=true) ∧ True := by sorry
