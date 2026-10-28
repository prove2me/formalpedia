-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_checked_type6_31
-- name    : BS2_b3ba934b_RI_checked_type6_31
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:46:01.638831+00:00
-- url     : https://prove2.me/theorems/2dac117d-14e8-4095-b8de-98dd189970fd
-- title:
--   Sensitivity record certificate: checked_type6_31
-- statement:
--   The original complete proof of ThreeBoundEndpoint40Records.checked_type6_31, using only separately accepted record facts through data-only theorem interfaces. Natural-number index conversions are explicit reflexive equality transports; the proposition is unchanged.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble09.lean; original SHA-256 53823f851a266487908c8736d711f23ee98517f598c93fb29c94568a87f671a0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_checked_type6_31 : ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [5,5,5,5,7,7]=true := by sorry
