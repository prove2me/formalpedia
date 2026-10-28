-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_checked_type6_28_chunk0
-- name    : BS2_b3ba934b_RI_checked_type6_28_chunk0
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:43:24.612205+00:00
-- url     : https://prove2.me/theorems/06f9a9f8-7d67-4d05-8ec1-0a06c84e22ac
-- title:
--   Sensitivity record certificate: checked_type6_28_chunk0
-- statement:
--   The original complete proof of ThreeBoundEndpoint40Records.checked_type6_28_chunk0, using only separately accepted record facts through data-only theorem interfaces. Natural-number index conversions are explicit reflexive equality transports; the proposition is unchanged.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks059.lean; original SHA-256 8fc8923cb5f2a3e5c13928b8b8b424483b28231d12d750b62dd39835ae907b4d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_checked_type6_28_chunk0 : ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] 0 64=true := by sorry
