-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair2_3
-- name    : BS2_b3ba934b_Cert_40_RawPair2_3
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T05:51:36.912955+00:00
-- url     : https://prove2.me/theorems/bf3c6302-a827-4c5e-aac2-6f0d35afdf48
-- title:
--   Sensitivity separation: Endpoint40RawPair2_3 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair2_3. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair2_3.lean; original SHA-256 53e07756f7553e72edd19b18303c43166b0a708418adc66db309728730a0bbe9; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair2_3 : (rawAExpr 40 caps records (recipe 2 0) (recipe 2 3)).eval profile2≤333228916662993117187787030000000000000000000000000000000000000000000000 := by sorry
