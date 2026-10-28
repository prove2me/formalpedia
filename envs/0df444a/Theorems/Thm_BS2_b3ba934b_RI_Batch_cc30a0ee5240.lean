-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_cc30a0ee5240
-- name    : BS2_b3ba934b_RI_Batch_cc30a0ee5240
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:16:04.430995+00:00
-- url     : https://prove2.me/theorems/1239a349-0928-483c-8c39-e2bc75d47149
-- title:
--   Sensitivity record certificate: Batch_cc30a0ee5240
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type6_2, checked_type6_3, checked_type6_4, checked_type6_5, checked_type6_6, checked_type6_7, checked_type6_8, checked_type6_9. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble06.lean; original SHA-256 ca1f18636ba26d42cc66edc211b64878a82c0529e572e21c939bdaa76660fc2e; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_cc30a0ee5240 : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,4,5,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,5,5,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,5,5,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,2,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,4,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,5,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,5,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,3,5,5,5,5]=true) ∧ True := by sorry
