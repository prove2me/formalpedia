-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_28
-- name    : BS2_b3ba934b_Cert_40_RawPair1_28
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T03:46:25.32556+00:00
-- url     : https://prove2.me/theorems/9844d5f6-675e-4d77-b4dc-d7d00011e2d2
-- title:
--   Sensitivity separation: Endpoint40RawPair1_28 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_28. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_28.lean; original SHA-256 33ab8d7abd42e73f3c66894b0aac6b57f89cef445ebf267e117bb6389e84d235; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_28 : (rawAExpr 40 caps records (recipe 1 3) (recipe 1 9)).eval profile1≤45306527546439468734521540000000000000000000000000000000000000000000000 := by sorry
