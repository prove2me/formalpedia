-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawNumerical1
-- name    : BS2_b3ba934b_Cert_40_RawNumerical1
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T05:04:25.488543+00:00
-- url     : https://prove2.me/theorems/7e88c1cd-aed7-448f-8e08-84397b159d87
-- title:
--   Sensitivity separation: Endpoint40RawProof1 raw_numerical checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawProof1. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawProof1.lean; original SHA-256 72e59a2b0098ca1eccdc5e74fe2a14341af177f1a233bc3323d547569b5e1922; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawNumerical1 (coord : Coord 40) (h : valid coord) :
    raw 1 profile1 coord≤rawProfile1 coord := by sorry
