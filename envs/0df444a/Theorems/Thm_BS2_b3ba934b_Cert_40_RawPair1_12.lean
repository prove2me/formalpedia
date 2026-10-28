-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_12
-- name    : BS2_b3ba934b_Cert_40_RawPair1_12
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T02:05:38.574818+00:00
-- url     : https://prove2.me/theorems/0aa9096b-6e09-4b53-a2fe-839b6e2319f5
-- title:
--   Sensitivity separation: Endpoint40RawPair1_12 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_12. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_12.lean; original SHA-256 7cae9ca3181ebdfbe5fa41828e6d681082418b814934bc751c8be0d7ad433923; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_12 : (rawAExpr 40 caps records (recipe 1 0) (recipe 1 5)).eval profile1≤38398877794827724331410000000000000000000000000000000000000000000000 := by sorry
