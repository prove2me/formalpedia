-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_36
-- name    : BS2_b3ba934b_Cert_40_RawPair1_36
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T04:14:13.640015+00:00
-- url     : https://prove2.me/theorems/dcb4453e-23fd-4edd-980c-f511058d0118
-- title:
--   Sensitivity separation: Endpoint40RawPair1_36 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_36. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_36.lean; original SHA-256 27911241bcfa041d9745f40997c56311d40f9508fd8db00ecc77c6a6c415ed27; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_36 : (rawAExpr 40 caps records (recipe 1 3) (recipe 1 10)).eval profile1≤45306527546439468734521540000000000000000000000000000000000000000000000 := by sorry
