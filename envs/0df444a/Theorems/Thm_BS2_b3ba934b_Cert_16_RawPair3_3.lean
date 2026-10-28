-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair3_3
-- name    : BS2_b3ba934b_Cert_16_RawPair3_3
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:30:07.426448+00:00
-- url     : https://prove2.me/theorems/1edf90a1-08ea-4090-a4f9-9d0f4a22ab82
-- title:
--   Sensitivity separation: Endpoint16RawPair3_3 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawPair3_3. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawPair3_3.lean; original SHA-256 fdcb1ab3e48b5fcdab42ddd26eaa4fb6ff098936bab24f753d6fd68fe59ccad3; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawPair3_3 : (ThreeBoundMinmaxA.rawAExpr 16 caps records
    (recipe 3 3) (recipe 3 3)).eval profile3≤1076339290179921391893340797180000000000000000000000000000000000000000000000 := by sorry
