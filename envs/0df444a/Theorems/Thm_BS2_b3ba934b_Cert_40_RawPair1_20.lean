-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_20
-- name    : BS2_b3ba934b_Cert_40_RawPair1_20
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T03:03:13.847335+00:00
-- url     : https://prove2.me/theorems/3d15b790-64d9-495b-b45d-d071d36d0e56
-- title:
--   Sensitivity separation: Endpoint40RawPair1_20 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_20. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_20.lean; original SHA-256 6e1ebf2c4a214e4c552280601965c19e011c33347892ad8381a228295c5edc6d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_20 : (rawAExpr 40 caps records (recipe 1 2) (recipe 1 7)).eval profile1≤38398877794827724331410000000000000000000000000000000000000000000000 := by sorry
