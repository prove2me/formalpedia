-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair3_7
-- name    : BS2_b3ba934b_Cert_40_RawPair3_7
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T07:04:15.403432+00:00
-- url     : https://prove2.me/theorems/84f278c2-b893-4437-8e82-61317f63ce93
-- title:
--   Sensitivity separation: Endpoint40RawPair3_7 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair3_7. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair3_7.lean; original SHA-256 2a02fe373fb260a67704849204736b33da601ac40c8e5fb5183835247eaee589; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair3_7 : (rawAExpr 40 caps records (recipe 3 3) (recipe 3 4)).eval profile3≤25006000113424645102729645880000000000000000000000000000000000000000000000 := by sorry
