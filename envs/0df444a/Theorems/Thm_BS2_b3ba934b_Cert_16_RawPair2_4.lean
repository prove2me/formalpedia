-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair2_4
-- name    : BS2_b3ba934b_Cert_16_RawPair2_4
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:29:39.134992+00:00
-- url     : https://prove2.me/theorems/c58d0453-daee-4787-aeda-a1d5bcef2e42
-- title:
--   Sensitivity separation: Endpoint16RawPair2_4 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawPair2_4. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawPair2_4.lean; original SHA-256 dbb51f7668caf87e0b0a8e8c0e5630323c691f9cdc6f24ca194ab79aec069594; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawPair2_4 : (ThreeBoundMinmaxA.rawAExpr 16 caps records
    (recipe 2 1) (recipe 2 3)).eval profile2≤661465889144801567244956340000000000000000000000000000000000000000000000 := by sorry
