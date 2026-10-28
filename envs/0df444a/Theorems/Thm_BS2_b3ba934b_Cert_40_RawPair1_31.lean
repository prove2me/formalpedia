-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_31
-- name    : BS2_b3ba934b_Cert_40_RawPair1_31
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T03:56:22.590143+00:00
-- url     : https://prove2.me/theorems/0313698a-7543-4e2e-bddd-33347ce5e800
-- title:
--   Sensitivity separation: Endpoint40RawPair1_31 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_31. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_31.lean; original SHA-256 300943e32e37eabb2f46607d1436b69c62318f617c86a61fe7c60f5e4130016c; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_31 : (rawAExpr 40 caps records (recipe 1 7) (recipe 1 9)).eval profile1≤45306527546439468734521540000000000000000000000000000000000000000000000 := by sorry
