-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_checked_type6_29_chunk1600
-- name    : BS2_b3ba934b_RI_checked_type6_29_chunk1600
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:33:19.992511+00:00
-- url     : https://prove2.me/theorems/c7d0a671-d0eb-473f-b8ce-369164c4b554
-- title:
--   Sensitivity record certificate: checked_type6_29_chunk1600
-- statement:
--   The original complete proof of ThreeBoundEndpoint40Records.checked_type6_29_chunk1600, using only separately accepted record facts through data-only theorem interfaces. Natural-number index conversions are explicit reflexive equality transports; the proposition is unchanged.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks062.lean; original SHA-256 41d174b0041abc637597ec1868d67eda8a4f986f9f3bfe4311d36bc491e269b4; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_checked_type6_29_chunk1600 : ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1600 64=true := by sorry
