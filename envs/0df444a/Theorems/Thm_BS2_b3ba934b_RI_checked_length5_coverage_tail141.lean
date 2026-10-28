-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_checked_length5_coverage_tail141
-- name    : BS2_b3ba934b_RI_checked_length5_coverage_tail141
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:42:25.101991+00:00
-- url     : https://prove2.me/theorems/a92779e8-3f2d-467f-9f75-17d2a2dd8e04
-- title:
--   Sensitivity record certificate: checked_length5_coverage_tail141
-- statement:
--   The original complete proof of ThreeBoundEndpoint40Records.checked_length5_coverage_tail141, using only separately accepted record facts through data-only theorem interfaces. Natural-number index conversions are explicit reflexive equality transports; the proposition is unchanged.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordCoverage.lean; original SHA-256 c0cbb975d0b32d8bfeba818e4c16919ab962fa66af5f94a14b4cb925832b8510; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_checked_length5_coverage_tail141 : (([[5,5,5,5,5],[5,5,5,5,6],[5,5,5,5,7],[5,5,5,6,6],[5,5,5,6,7],[5,5,5,7,7],[5,5,6,6,7],[5,5,6,7,7],[5,5,7,7,7],[5,6,7,7,7],[5,7,7,7,7],[7,7,7,7,7]] : List (List ThreeBoundQ2.Kind)).all (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree))=true := by sorry
