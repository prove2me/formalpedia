-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair1_1
-- name    : BS2_b3ba934b_Cert_16_RawPair1_1
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:29:12.283627+00:00
-- url     : https://prove2.me/theorems/c4721421-926e-467f-8c6a-b14d525bd9e2
-- title:
--   Sensitivity separation: Endpoint16RawPair1_1 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawPair1_1. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawPair1_1.lean; original SHA-256 12ff333f9904b720aa673f315f7ba38bc5782359b87e3e248971951a4ac48592; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawPair1_1 : (ThreeBoundMinmaxA.rawAExpr 16 caps records
    (recipe 1 1) (recipe 1 2)).eval profile1≤11659749300103673188588500000000000000000000000000000000000000000000000 := by sorry
