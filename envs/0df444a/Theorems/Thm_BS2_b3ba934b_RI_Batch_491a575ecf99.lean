-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_491a575ecf99
-- name    : BS2_b3ba934b_RI_Batch_491a575ecf99
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:18:54.967964+00:00
-- url     : https://prove2.me/theorems/4e400631-007f-4f11-aaa3-1b656a0c191d
-- title:
--   Sensitivity record certificate: Batch_491a575ecf99
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type5_10, checked_type5_11, checked_type5_12, checked_type5_13, checked_type5_14, checked_type5_15, checked_type5_16, checked_type5_17, checked_type5_18, checked_type5_7, checked_type5_8, checked_type5_9. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks017.lean; original SHA-256 3091a559c328db30e2788c533cbbc90605a69a00dfbb11eac9020611cb91187d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_491a575ecf99 : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [0,5,5,5,6]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [0,5,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [0,5,5,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,1,2,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,1,4,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,1,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,1,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,2,2,2,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,2,2,4,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [0,4,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [0,4,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [0,5,5,5,5]=true) ∧ True := by sorry
