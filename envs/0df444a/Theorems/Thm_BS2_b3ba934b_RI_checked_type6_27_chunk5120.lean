-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_checked_type6_27_chunk5120
-- name    : BS2_b3ba934b_RI_checked_type6_27_chunk5120
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:40:10.447587+00:00
-- url     : https://prove2.me/theorems/d266c1cc-1808-4083-bcd2-28113b74e873
-- title:
--   Sensitivity record certificate: checked_type6_27_chunk5120
-- statement:
--   The original complete proof of ThreeBoundEndpoint40Records.checked_type6_27_chunk5120, using only separately accepted record facts through data-only theorem interfaces. Natural-number index conversions are explicit reflexive equality transports; the proposition is unchanged.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks059.lean; original SHA-256 8fc8923cb5f2a3e5c13928b8b8b424483b28231d12d750b62dd39835ae907b4d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_checked_type6_27_chunk5120 : ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 5120 64=true := by sorry
