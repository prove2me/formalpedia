-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_8b120256d811
-- name    : BS2_b3ba934b_RI_Batch_8b120256d811
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:14:53.793461+00:00
-- url     : https://prove2.me/theorems/178c4472-afd7-467e-827d-64027b2176aa
-- title:
--   Sensitivity record certificate: Batch_8b120256d811
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: activeTypes6_eq. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordCoverage.lean; original SHA-256 c0cbb975d0b32d8bfeba818e4c16919ab962fa66af5f94a14b4cb925832b8510; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_8b120256d811 : (ThreeBoundRecordLookup.activeTypes 6 = [
[0,5,5,5,5,5],
[1,2,5,5,5,5],
[1,4,5,5,5,5],
[1,5,5,5,5,5],
[1,5,5,5,5,7],
[2,2,2,5,5,5],
[2,2,4,5,5,5],
[2,2,5,5,5,5],
[2,2,5,5,5,7],
[2,3,5,5,5,5],
[2,4,4,5,5,5],
[2,4,5,5,5,5],
[2,4,5,5,5,7],
[2,5,5,5,5,5],
[2,5,5,5,5,6],
[2,5,5,5,5,7],
[2,5,5,5,7,7],
[3,4,5,5,5,5],
[3,5,5,5,5,5],
[3,5,5,5,5,7],
[4,4,4,5,5,5],
[4,4,5,5,5,5],
[4,4,5,5,5,7],
[4,5,5,5,5,5],
[4,5,5,5,5,6],
[4,5,5,5,5,7],
[4,5,5,5,7,7],
[5,5,5,5,5,5],
[5,5,5,5,5,6],
[5,5,5,5,5,7],
[5,5,5,5,6,7],
[5,5,5,5,7,7],
[5,5,5,7,7,7]]) ∧ True := by sorry
