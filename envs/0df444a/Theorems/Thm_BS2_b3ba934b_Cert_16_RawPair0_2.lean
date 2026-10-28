-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair0_2
-- name    : BS2_b3ba934b_Cert_16_RawPair0_2
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:29:44.58222+00:00
-- url     : https://prove2.me/theorems/d64afc7b-a9a2-4a75-ae5e-79d3a1355e47
-- title:
--   Sensitivity separation: Endpoint16RawPair0_2 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawPair0_2. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawPair0_2.lean; original SHA-256 e704ec8fc1c3a35798fd4fd24f43b434a17d2c0e26c7fd3ddde87535316e1733; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawPair0_2 : (ThreeBoundMinmaxA.rawAExpr 16 caps records
    (recipe 0 0) (recipe 0 2)).eval profile0≤118398645020199144745000000000000000000000000000000000000000000000000 := by sorry
