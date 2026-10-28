-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_5f639105d24c
-- name    : BS2_b3ba934b_RI_Batch_5f639105d24c
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:21:17.305834+00:00
-- url     : https://prove2.me/theorems/bee0cf66-c1e9-4389-ad96-8871953fb066
-- title:
--   Sensitivity record certificate: Batch_5f639105d24c
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type5_49, checked_type5_50, checked_type5_52, checked_type5_54, checked_type5_56. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks021.lean; original SHA-256 a4c6f49de3e9dcb5a2a148f6315d5a86ff4989b1a9cf77ff48d116758e47a811; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_5f639105d24c : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,2,3,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,2,4,4]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,2,4,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,2,5,6]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,2,7,7]=true) ∧ True := by sorry
