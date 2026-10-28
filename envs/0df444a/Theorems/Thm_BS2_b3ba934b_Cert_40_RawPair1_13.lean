-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_13
-- name    : BS2_b3ba934b_Cert_40_RawPair1_13
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T02:07:55.777461+00:00
-- url     : https://prove2.me/theorems/05e666fd-9ffd-436c-b526-3f004941beb7
-- title:
--   Sensitivity separation: Endpoint40RawPair1_13 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_13. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_13.lean; original SHA-256 55e95146b96e3ef9f4e70df96cbab0c1b9a885207c6dbd7e5d95252a518b9fcc; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_13 : (rawAExpr 40 caps records (recipe 1 1) (recipe 1 5)).eval profile1≤38398877794827724331410000000000000000000000000000000000000000000000 := by sorry
