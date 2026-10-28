-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_83689d4e5d10
-- name    : BS2_b3ba934b_RI_Batch_83689d4e5d10
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:32:11.403649+00:00
-- url     : https://prove2.me/theorems/6d49ab4c-a278-46c1-9513-210841731a0b
-- title:
--   Sensitivity record certificate: Batch_83689d4e5d10
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type5_141, checked_type5_142, checked_type5_143, checked_type5_145, checked_type5_146, checked_type5_149, checked_type5_151, checked_type6_1. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble05.lean; original SHA-256 cdcd6c327a1b2e8ea5359f5dce70a2ed50cd12bfaa155b48b1ced080fc70fa18; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_83689d4e5d10 : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [5,5,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [5,5,5,5,6]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [5,5,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [5,5,5,6,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [5,5,5,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [5,5,7,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [5,7,7,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,2,5,5,5,5]=true) ∧ True := by sorry
