-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair3_1
-- name    : BS2_b3ba934b_Cert_40_RawPair3_1
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T06:39:55.630735+00:00
-- url     : https://prove2.me/theorems/93c9d34b-b65f-4e14-bcce-0b1a09170346
-- title:
--   Sensitivity separation: Endpoint40RawPair3_1 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair3_1. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair3_1.lean; original SHA-256 ef445862623a77b16c9c38fb5efb4f9f4f90c1eff94e8adaaceacd9994455d55; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair3_1 : (rawAExpr 40 caps records (recipe 3 1) (recipe 3 3)).eval profile3≤32945822928780164219782456170000000000000000000000000000000000000000000000 := by sorry
