-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_f65539825b42
-- name    : BS2_b3ba934b_RI_Batch_f65539825b42
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:27:03.266411+00:00
-- url     : https://prove2.me/theorems/91c6605f-5b49-4054-b40a-eccd7babe10a
-- title:
--   Sensitivity record certificate: Batch_f65539825b42
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type5_84, checked_type5_86, checked_type5_88, checked_type5_90, checked_type5_92, checked_type5_94, checked_type5_95, checked_type5_96. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble02.lean; original SHA-256 375e36acb8fab523b056aaba5e9305c5fc1e9741fde09fe81403cf733694286c; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_f65539825b42 : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,4,4,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,4,4,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,4,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,4,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,4,5,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,5,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,5,5,5,6]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,5,5,5,7]=true) ∧ True := by sorry
