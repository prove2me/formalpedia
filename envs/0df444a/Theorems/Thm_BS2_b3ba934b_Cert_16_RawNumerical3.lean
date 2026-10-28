-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawNumerical3
-- name    : BS2_b3ba934b_Cert_16_RawNumerical3
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:31:55.243979+00:00
-- url     : https://prove2.me/theorems/583f756b-923a-469f-8692-a574e15d7f7a
-- title:
--   Sensitivity separation: Endpoint16RawProof3 raw_numerical checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawProof3. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawProof3.lean; original SHA-256 539c53bed447ae5c6ed37397bf1e9675200da15133afd04107cc772283d3f314; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawNumerical3 (coord : Coord 16) (h : valid coord) :
    raw 3 profile3 coord≤rawProfile3 coord := by sorry
