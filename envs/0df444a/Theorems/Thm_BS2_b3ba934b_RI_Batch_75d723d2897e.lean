-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_75d723d2897e
-- name    : BS2_b3ba934b_RI_Batch_75d723d2897e
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:32:23.662412+00:00
-- url     : https://prove2.me/theorems/4be3a7e5-2119-4994-8614-f3c295e89d9b
-- title:
--   Sensitivity record certificate: Batch_75d723d2897e
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_type6_26. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble09.lean; original SHA-256 53823f851a266487908c8736d711f23ee98517f598c93fb29c94568a87f671a0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_75d723d2897e : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,5,5,5,7,7]=true) ∧ True := by sorry
