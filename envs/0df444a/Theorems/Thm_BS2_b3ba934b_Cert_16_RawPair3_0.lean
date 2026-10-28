-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair3_0
-- name    : BS2_b3ba934b_Cert_16_RawPair3_0
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:29:58.207823+00:00
-- url     : https://prove2.me/theorems/174f38c8-bdc4-4797-9ddf-2f4062be9208
-- title:
--   Sensitivity separation: Endpoint16RawPair3_0 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawPair3_0. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawPair3_0.lean; original SHA-256 532dd6e8394d8dbe93e08653d0f5e95d1123ac11e6600e5655fb94aaca47fc60; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawPair3_0 : (ThreeBoundMinmaxA.rawAExpr 16 caps records
    (recipe 3 0) (recipe 3 3)).eval profile3≤65136953840227306262442285060000000000000000000000000000000000000000000000 := by sorry
