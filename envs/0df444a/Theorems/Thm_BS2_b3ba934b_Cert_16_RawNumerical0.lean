-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawNumerical0
-- name    : BS2_b3ba934b_Cert_16_RawNumerical0
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:28:51.631083+00:00
-- url     : https://prove2.me/theorems/b066a182-5320-4089-9481-03a0f74eecbc
-- title:
--   Sensitivity separation: Endpoint16RawProof0 raw_numerical checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawProof0. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawProof0.lean; original SHA-256 69fc765c38fd207decac7eddb39f39d683909d7ea74eed806ed2c3aa57dd71d2; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawNumerical0 (coord : Coord 16) (h : valid coord) :
    raw 0 profile0 coord≤rawProfile0 coord := by sorry
