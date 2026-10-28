-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair3_5
-- name    : BS2_b3ba934b_Cert_16_RawPair3_5
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:30:53.291993+00:00
-- url     : https://prove2.me/theorems/83a86d9e-d6e4-411f-be93-a031de4de6d6
-- title:
--   Sensitivity separation: Endpoint16RawPair3_5 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawPair3_5. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawPair3_5.lean; original SHA-256 4a2979af098d30d471edc8d44e7b66c0b00dc1bce2c63987429cc505cd589ce1; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawPair3_5 : (ThreeBoundMinmaxA.rawAExpr 16 caps records
    (recipe 3 1) (recipe 3 4)).eval profile3≤49435378198966834859642266240000000000000000000000000000000000000000000000 := by sorry
