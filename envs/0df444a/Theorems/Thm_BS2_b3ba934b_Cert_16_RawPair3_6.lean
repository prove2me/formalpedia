-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair3_6
-- name    : BS2_b3ba934b_Cert_16_RawPair3_6
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:30:16.746036+00:00
-- url     : https://prove2.me/theorems/90507f33-6949-4f0e-bbb5-a808581d4129
-- title:
--   Sensitivity separation: Endpoint16RawPair3_6 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawPair3_6. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawPair3_6.lean; original SHA-256 48780e4069822f871a1bf612be4103f3bbe74917a06e551f2696be6356fc86ff; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawPair3_6 : (ThreeBoundMinmaxA.rawAExpr 16 caps records
    (recipe 3 2) (recipe 3 4)).eval profile3≤49435378198966834859642266240000000000000000000000000000000000000000000000 := by sorry
