-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_41
-- name    : BS2_b3ba934b_Cert_40_RawPair1_41
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T04:35:16.848991+00:00
-- url     : https://prove2.me/theorems/726abdb5-eb52-4a3f-90d8-f27e5ca466d0
-- title:
--   Sensitivity separation: Endpoint40RawPair1_41 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_41. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_41.lean; original SHA-256 760220b33a5372ceb39f8bc349372ee4c8cf269bc5aa3aae43c1387ece6ff270; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_41 : (rawAExpr 40 caps records (recipe 1 10) (recipe 1 10)).eval profile1≤45306527546439468734521540000000000000000000000000000000000000000000000 := by sorry
