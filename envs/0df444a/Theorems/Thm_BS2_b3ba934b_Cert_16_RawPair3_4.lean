-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair3_4
-- name    : BS2_b3ba934b_Cert_16_RawPair3_4
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:28:58.206533+00:00
-- url     : https://prove2.me/theorems/02eef0ad-b589-4932-8ff4-c2cecabaa01e
-- title:
--   Sensitivity separation: Endpoint16RawPair3_4 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawPair3_4. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawPair3_4.lean; original SHA-256 395ba5d8e9ce88f56a8da8dac6ad339d6d6474cb3433a1fd61ed63230181fe41; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawPair3_4 : (ThreeBoundMinmaxA.rawAExpr 16 caps records
    (recipe 3 0) (recipe 3 4)).eval profile3≤49435378198966834859642266240000000000000000000000000000000000000000000000 := by sorry
