-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair0_1
-- name    : BS2_b3ba934b_Cert_16_RawPair0_1
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:29:29.10322+00:00
-- url     : https://prove2.me/theorems/e6c9b240-2b30-4cb8-be5a-89a61b3edc25
-- title:
--   Sensitivity separation: Endpoint16RawPair0_1 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawPair0_1. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawPair0_1.lean; original SHA-256 139f68bcdd2f9135b5a9e69f9e5a0dbb230c8a19ad1a90dba1bae38d7719fff4; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawPair0_1 : (ThreeBoundMinmaxA.rawAExpr 16 caps records
    (recipe 0 1) (recipe 0 1)).eval profile0≤2579858090809581183210000000000000000000000000000000000000000000000000 := by sorry
