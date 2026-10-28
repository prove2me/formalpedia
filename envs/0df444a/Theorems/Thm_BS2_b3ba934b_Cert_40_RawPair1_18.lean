-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_18
-- name    : BS2_b3ba934b_Cert_40_RawPair1_18
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T02:40:28.366981+00:00
-- url     : https://prove2.me/theorems/b967e039-814e-47ce-9026-9fa56a077604
-- title:
--   Sensitivity separation: Endpoint40RawPair1_18 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_18. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_18.lean; original SHA-256 76468b4a3c6b8798dd070f630cc4a282aa22b9cfa3befbebaa92953ee79a7419; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_18 : (rawAExpr 40 caps records (recipe 1 0) (recipe 1 7)).eval profile1≤38398877794827724331410000000000000000000000000000000000000000000000 := by sorry
