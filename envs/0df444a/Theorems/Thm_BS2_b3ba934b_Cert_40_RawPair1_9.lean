-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_9
-- name    : BS2_b3ba934b_Cert_40_RawPair1_9
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:51:47.277998+00:00
-- url     : https://prove2.me/theorems/c27fea2e-e06f-4335-9460-e8e4880e9f0a
-- title:
--   Sensitivity separation: Endpoint40RawPair1_9 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_9. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_9.lean; original SHA-256 89f255bbe13888dc521234e09bb722088025465fdd14d637cb0373cf2bedf9c1; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_9 : (rawAExpr 40 caps records (recipe 1 2) (recipe 1 4)).eval profile1≤4440088403177649112679030000000000000000000000000000000000000000000000 := by sorry
