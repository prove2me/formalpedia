-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_1
-- name    : BS2_b3ba934b_Cert_40_RawPair1_1
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:23:21.958293+00:00
-- url     : https://prove2.me/theorems/115db5ad-84bd-4eca-983d-8cedcb72cffe
-- title:
--   Sensitivity separation: Endpoint40RawPair1_1 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_1. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_1.lean; original SHA-256 35ad7681a4a3433e85b313b420a8fdcae62e3c34f4c31e35c63d96b66e887f82; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_1 : (rawAExpr 40 caps records (recipe 1 1) (recipe 1 2)).eval profile1≤5849894674075950384437030000000000000000000000000000000000000000000000 := by sorry
