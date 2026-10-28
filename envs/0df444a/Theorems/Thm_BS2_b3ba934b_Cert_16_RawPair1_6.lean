-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair1_6
-- name    : BS2_b3ba934b_Cert_16_RawPair1_6
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:29:03.356033+00:00
-- url     : https://prove2.me/theorems/d2096098-71f7-447f-b98c-5d229147fb5a
-- title:
--   Sensitivity separation: Endpoint16RawPair1_6 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawPair1_6. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawPair1_6.lean; original SHA-256 979bbb26c71ec98ee14409a0e009f1fca2231f002227497a08aa87ba7badee27; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawPair1_6 : (ThreeBoundMinmaxA.rawAExpr 16 caps records
    (recipe 1 3) (recipe 1 3)).eval profile1≤98629719959159679536468500000000000000000000000000000000000000000000000 := by sorry
