-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_checked_type6_30_chunk64
-- name    : BS2_b3ba934b_RI_checked_type6_30_chunk64
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:33:58.851977+00:00
-- url     : https://prove2.me/theorems/2f665499-38f7-4671-8509-9bceb65d4138
-- title:
--   Sensitivity record certificate: checked_type6_30_chunk64
-- statement:
--   The original complete proof of ThreeBoundEndpoint40Records.checked_type6_30_chunk64, using only separately accepted record facts through data-only theorem interfaces. Natural-number index conversions are explicit reflexive equality transports; the proposition is unchanged.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks063.lean; original SHA-256 be473fbf748907b12f5977b479be61994a26245bca16188173dfe2b2df4c0721; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_checked_type6_30_chunk64 : ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,6,7] 64 16=true := by sorry
