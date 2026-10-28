-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_73dc4d6e4e00
-- name    : BS2_b3ba934b_RI_Batch_73dc4d6e4e00
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:26:43.594397+00:00
-- url     : https://prove2.me/theorems/87ff22d3-fa66-4b2f-a705-22b12bd39ec7
-- title:
--   Sensitivity record certificate: Batch_73dc4d6e4e00
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type5_57, checked_type5_58, checked_type5_59, checked_type5_60, checked_type5_62, checked_type5_64. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks022.lean; original SHA-256 7009069ffab199f6718259b8057948d1e6ac666bec98ccde95d7e297732c482e; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_73dc4d6e4e00 : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,3,4,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,3,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,3,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,4,4,4]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,4,4,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,4,5,6]=true) ∧ True := by sorry
