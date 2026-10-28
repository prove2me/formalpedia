-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_6ceda367be65
-- name    : BS2_b3ba934b_RI_Batch_6ceda367be65
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:27:31.309774+00:00
-- url     : https://prove2.me/theorems/ae49f823-6de0-41f6-86ce-ce971bd43d5d
-- title:
--   Sensitivity record certificate: Batch_6ceda367be65
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type5_126, checked_type5_128, checked_type5_130, checked_type5_132, checked_type5_133, checked_type5_134, checked_type5_137, checked_type5_139. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble04.lean; original SHA-256 c1d124b2e5c1f9a0cde9acf371a9afd66dec57261d17e698b5e8b734b44b76a6; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_6ceda367be65 : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,4,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,4,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,4,5,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,5,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,5,5,5,6]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,5,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,5,5,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,5,7,7,7]=true) ∧ True := by sorry
