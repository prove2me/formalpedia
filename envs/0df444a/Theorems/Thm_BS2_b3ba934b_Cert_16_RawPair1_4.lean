-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair1_4
-- name    : BS2_b3ba934b_Cert_16_RawPair1_4
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:29:21.883897+00:00
-- url     : https://prove2.me/theorems/bc1bbf70-ada3-4d51-ba5a-4eb08e015232
-- title:
--   Sensitivity separation: Endpoint16RawPair1_4 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawPair1_4. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawPair1_4.lean; original SHA-256 891a2e6e8bd521dff398b7c06721aee776799f17e320550c58acbef067e58c52; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawPair1_4 : (ThreeBoundMinmaxA.rawAExpr 16 caps records
    (recipe 1 1) (recipe 1 3)).eval profile1≤8848850045846562315998500000000000000000000000000000000000000000000000 := by sorry
