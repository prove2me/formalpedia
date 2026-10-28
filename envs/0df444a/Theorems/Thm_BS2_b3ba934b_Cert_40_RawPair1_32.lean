-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_32
-- name    : BS2_b3ba934b_Cert_40_RawPair1_32
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T03:59:26.341969+00:00
-- url     : https://prove2.me/theorems/cf17bbbb-fe29-4432-ba42-061f313bf902
-- title:
--   Sensitivity separation: Endpoint40RawPair1_32 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_32. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_32.lean; original SHA-256 446016db54ade21976de0ed65712914d2cf7d9ce25418014c1cbd2b8f32eb6e2; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_32 : (rawAExpr 40 caps records (recipe 1 9) (recipe 1 9)).eval profile1≤45306527546439468734521540000000000000000000000000000000000000000000000 := by sorry
