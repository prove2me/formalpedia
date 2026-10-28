-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_096097d3be29
-- name    : BS2_b3ba934b_RI_Batch_096097d3be29
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:20:53.79003+00:00
-- url     : https://prove2.me/theorems/3147a230-c7f0-41ae-b3ed-13e20302757b
-- title:
--   Sensitivity record certificate: Batch_096097d3be29
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type5_40, checked_type5_42, checked_type5_43, checked_type5_44, checked_type5_45, checked_type5_46, checked_type5_48. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks020.lean; original SHA-256 9950ff0914ff82962e1f19720016d60be87b0713142519caefc010905643f295; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_096097d3be29 : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,5,5,5,6]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,5,5,6,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,5,5,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,5,7,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,2,2,2]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,2,2,4]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,2,2,7]=true) ∧ True := by sorry
