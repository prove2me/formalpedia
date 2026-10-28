-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_9c087f987607
-- name    : BS2_b3ba934b_RI_Batch_9c087f987607
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:26:48.584026+00:00
-- url     : https://prove2.me/theorems/ce2a20a4-75e5-4dd6-9639-081dbea007dd
-- title:
--   Sensitivity record certificate: Batch_9c087f987607
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type5_61, checked_type5_63, checked_type5_65, checked_type5_67, checked_type5_69, checked_type5_71, checked_type5_77, checked_type5_82. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble01.lean; original SHA-256 ed04fcee2d50e10d097119e93ebed3efb892b3154207f43cac8e0def4ed341cf; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_9c087f987607 : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,4,4,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,4,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,4,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,5,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,3,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,4,4,4,5]=true) ∧ True := by sorry
