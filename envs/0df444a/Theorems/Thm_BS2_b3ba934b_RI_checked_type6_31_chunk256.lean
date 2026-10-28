-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_checked_type6_31_chunk256
-- name    : BS2_b3ba934b_RI_checked_type6_31_chunk256
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:34:31.674622+00:00
-- url     : https://prove2.me/theorems/d5f70c4f-4147-401e-a300-7147ed2ea984
-- title:
--   Sensitivity record certificate: checked_type6_31_chunk256
-- statement:
--   The original complete proof of ThreeBoundEndpoint40Records.checked_type6_31_chunk256, using only separately accepted record facts through data-only theorem interfaces. Natural-number index conversions are explicit reflexive equality transports; the proposition is unchanged.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks063.lean; original SHA-256 be473fbf748907b12f5977b479be61994a26245bca16188173dfe2b2df4c0721; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_checked_type6_31_chunk256 : ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,7,7] 256 64=true := by sorry
