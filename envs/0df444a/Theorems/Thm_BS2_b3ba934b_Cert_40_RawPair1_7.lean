-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_7
-- name    : BS2_b3ba934b_Cert_40_RawPair1_7
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:46:11.311491+00:00
-- url     : https://prove2.me/theorems/77cbea18-59fb-453d-90ee-4eb986659134
-- title:
--   Sensitivity separation: Endpoint40RawPair1_7 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_7. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_7.lean; original SHA-256 cc75d2be096c7c6bbb8b4f93ff091568a011b5a1fdae989bbd3e0e52f93abde5; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_7 : (rawAExpr 40 caps records (recipe 1 0) (recipe 1 4)).eval profile1≤4440088403177649112679030000000000000000000000000000000000000000000000 := by sorry
