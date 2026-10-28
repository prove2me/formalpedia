-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_4
-- name    : BS2_b3ba934b_Cert_40_RawPair1_4
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:35:55.697144+00:00
-- url     : https://prove2.me/theorems/4fe3ea20-5702-4ee8-b22b-87e2651a6b0e
-- title:
--   Sensitivity separation: Endpoint40RawPair1_4 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_4. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_4.lean; original SHA-256 8e8144b1c2e1b7a78a78690d3e8a395f1b2f5621487237036aaae286ef4bbe07; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_4 : (rawAExpr 40 caps records (recipe 1 1) (recipe 1 3)).eval profile1≤5840625979435819554426000000000000000000000000000000000000000000000000 := by sorry
