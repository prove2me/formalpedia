-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawNumerical1
-- name    : BS2_b3ba934b_Cert_16_RawNumerical1
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:30:01.144298+00:00
-- url     : https://prove2.me/theorems/89627f99-fbf7-4430-878f-90d9aa127c1f
-- title:
--   Sensitivity separation: Endpoint16RawProof1 raw_numerical checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawProof1. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawProof1.lean; original SHA-256 b1d515f7bedd1f571892779beb6a1d5900f6ae7d9d8a93901f49f5e18733d56a; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawNumerical1 (coord : Coord 16) (h : valid coord) :
    raw 1 profile1 coord≤rawProfile1 coord := by sorry
