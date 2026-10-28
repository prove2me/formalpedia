-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_618c58463e44
-- name    : BS2_b3ba934b_RI_Batch_618c58463e44
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:32:13.534898+00:00
-- url     : https://prove2.me/theorems/1877cd86-8bff-4dbd-a740-93fcf8b5ec0d
-- title:
--   Sensitivity record certificate: Batch_618c58463e44
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type5_147, checked_type5_148, checked_type5_150, checked_type5_152, checked_type6_0. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks037.lean; original SHA-256 89df839c71b21b0380d88584df0a9cf167fa03529898e2e470242a565878444d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_618c58463e44 : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [5,5,6,6,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [5,5,6,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [5,6,7,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [7,7,7,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [0,5,5,5,5,5]=true) ∧ True := by sorry
