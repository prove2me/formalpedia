-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair0_4
-- name    : BS2_b3ba934b_Cert_16_RawPair0_4
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:29:39.086989+00:00
-- url     : https://prove2.me/theorems/c4aa2304-2b9e-4ec7-a9d9-d2606c9921ca
-- title:
--   Sensitivity separation: Endpoint16RawPair0_4 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawPair0_4. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawPair0_4.lean; original SHA-256 2956efc9e6c9f9e57150218a85416ddbf654269ade91269445fb8bf0d6e51c82; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawPair0_4 : (ThreeBoundMinmaxA.rawAExpr 16 caps records
    (recipe 0 2) (recipe 0 2)).eval profile0≤1319591558996649990745000000000000000000000000000000000000000000000000 := by sorry
