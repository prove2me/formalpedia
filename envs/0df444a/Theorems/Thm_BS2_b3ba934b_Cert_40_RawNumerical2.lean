-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawNumerical2
-- name    : BS2_b3ba934b_Cert_40_RawNumerical2
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T06:31:54.057503+00:00
-- url     : https://prove2.me/theorems/b714e013-eb8e-4140-bd56-23fa459015a0
-- title:
--   Sensitivity separation: Endpoint40RawProof2 raw_numerical checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawProof2. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawProof2.lean; original SHA-256 5c3795e111da5588d9d11d9eefb7938f801835b24c79c5f7b8e2fc1a7db5327d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawNumerical2 (coord : Coord 40) (h : valid coord) :
    raw 2 profile2 coord≤rawProfile2 coord := by sorry
