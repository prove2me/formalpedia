-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_113c145a94cf
-- name    : BS2_b3ba934b_RI_Batch_113c145a94cf
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:32:13.303434+00:00
-- url     : https://prove2.me/theorems/cf636cf9-9b4f-423e-b1a5-e30929472487
-- title:
--   Sensitivity record certificate: Batch_113c145a94cf
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type5_135. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks033.lean; original SHA-256 76dac2e9c62c3a173387c268778b650954786beb7eaed8fd7a77dcdda9967751; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_113c145a94cf : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,5,5,6,6]=true) ∧ True := by sorry
