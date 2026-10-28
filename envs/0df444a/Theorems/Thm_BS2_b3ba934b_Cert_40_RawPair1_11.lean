-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_11
-- name    : BS2_b3ba934b_Cert_40_RawPair1_11
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T02:00:59.849466+00:00
-- url     : https://prove2.me/theorems/ed8f46ef-f615-4bb1-b47a-696f60a42254
-- title:
--   Sensitivity separation: Endpoint40RawPair1_11 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_11. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_11.lean; original SHA-256 b470c1c2570f8eb42fbd56b47e4183d6a30a502b180777101e22fcb22e1b8acc; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_11 : (rawAExpr 40 caps records (recipe 1 4) (recipe 1 4)).eval profile1≤60742759185095740409372030000000000000000000000000000000000000000000000 := by sorry
