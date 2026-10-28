-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_c8f50db7233c
-- name    : BS2_b3ba934b_RI_Batch_c8f50db7233c
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:26:55.954916+00:00
-- url     : https://prove2.me/theorems/52465761-f66e-42d3-b107-b6fac623a52a
-- title:
--   Sensitivity record certificate: Batch_c8f50db7233c
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type5_72, checked_type5_73, checked_type5_74, checked_type5_75, checked_type5_76, checked_type5_78, checked_type5_79, checked_type5_80. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks024.lean; original SHA-256 7323c9addc9b42a37dc6fc73cbdf8c6fe897b16449a863564425519fc19322ce; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_c8f50db7233c : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,7,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,3,3,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,3,4,4,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,3,4,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,3,4,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,3,5,5,6]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,3,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,3,5,7,7]=true) ∧ True := by sorry
