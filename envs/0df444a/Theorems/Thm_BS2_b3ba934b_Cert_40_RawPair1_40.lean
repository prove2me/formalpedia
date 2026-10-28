-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_40
-- name    : BS2_b3ba934b_Cert_40_RawPair1_40
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T04:32:15.080561+00:00
-- url     : https://prove2.me/theorems/8f23dd2c-f7b5-4c7d-bae2-b4499393ef76
-- title:
--   Sensitivity separation: Endpoint40RawPair1_40 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_40. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_40.lean; original SHA-256 6fde2e1ec90544340c1f1f66fce45a6785180c360b1f3e6e4a5e7f4be572c1e2; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_40 : (rawAExpr 40 caps records (recipe 1 9) (recipe 1 10)).eval profile1≤45306527546439468734521540000000000000000000000000000000000000000000000 := by sorry
