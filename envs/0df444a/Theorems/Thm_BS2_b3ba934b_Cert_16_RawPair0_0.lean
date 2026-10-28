-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair0_0
-- name    : BS2_b3ba934b_Cert_16_RawPair0_0
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:29:15.88727+00:00
-- url     : https://prove2.me/theorems/1a56ec39-e22c-4e94-ac36-bd40b29a13a1
-- title:
--   Sensitivity separation: Endpoint16RawPair0_0 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawPair0_0. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawPair0_0.lean; original SHA-256 a18aaffa79a5b9d993a3231b7cc6e066d0089694a03bd5a426f8bce369bb7363; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawPair0_0 : (ThreeBoundMinmaxA.rawAExpr 16 caps records
    (recipe 0 0) (recipe 0 1)).eval profile0≤156008723698269154745000000000000000000000000000000000000000000000000 := by sorry
