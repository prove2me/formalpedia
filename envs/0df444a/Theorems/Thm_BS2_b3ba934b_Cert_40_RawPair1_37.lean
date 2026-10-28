-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_37
-- name    : BS2_b3ba934b_Cert_40_RawPair1_37
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T04:17:41.263981+00:00
-- url     : https://prove2.me/theorems/dc47e13c-f9db-4788-b7d9-b00bbcc824a4
-- title:
--   Sensitivity separation: Endpoint40RawPair1_37 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_37. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_37.lean; original SHA-256 d5df079df2228969c212232663d384d4d35d1fafed8b3ed4d25e90504ce6c2a5; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_37 : (rawAExpr 40 caps records (recipe 1 4) (recipe 1 10)).eval profile1≤45306527546439468734521540000000000000000000000000000000000000000000000 := by sorry
