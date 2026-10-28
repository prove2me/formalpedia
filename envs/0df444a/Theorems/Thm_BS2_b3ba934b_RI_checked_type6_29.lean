-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_checked_type6_29
-- name    : BS2_b3ba934b_RI_checked_type6_29
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:46:01.519301+00:00
-- url     : https://prove2.me/theorems/fed10c45-17cb-4f4e-9f2d-19346f4ca4d0
-- title:
--   Sensitivity record certificate: checked_type6_29
-- statement:
--   The original complete proof of ThreeBoundEndpoint40Records.checked_type6_29, using only separately accepted record facts through data-only theorem interfaces. Natural-number index conversions are explicit reflexive equality transports; the proposition is unchanged.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble09.lean; original SHA-256 53823f851a266487908c8736d711f23ee98517f598c93fb29c94568a87f671a0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_checked_type6_29 : ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7]=true := by sorry
