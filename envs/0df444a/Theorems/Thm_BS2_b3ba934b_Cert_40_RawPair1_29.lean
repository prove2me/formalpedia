-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_29
-- name    : BS2_b3ba934b_Cert_40_RawPair1_29
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T03:49:24.296692+00:00
-- url     : https://prove2.me/theorems/8cb4d54e-08f5-45b5-9c24-b8f0eca87154
-- title:
--   Sensitivity separation: Endpoint40RawPair1_29 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_29. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_29.lean; original SHA-256 1a48b5fc66b570452a1212cb545054b69dc9f8be7cbdb0b82a0f15012a5cc99a; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_29 : (rawAExpr 40 caps records (recipe 1 4) (recipe 1 9)).eval profile1≤45306527546439468734521540000000000000000000000000000000000000000000000 := by sorry
