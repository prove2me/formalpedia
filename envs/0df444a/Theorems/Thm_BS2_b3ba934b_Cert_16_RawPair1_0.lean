-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair1_0
-- name    : BS2_b3ba934b_Cert_16_RawPair1_0
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:29:13.931819+00:00
-- url     : https://prove2.me/theorems/bfe357d3-85d1-4f46-ab91-06459b8183ce
-- title:
--   Sensitivity separation: Endpoint16RawPair1_0 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawPair1_0. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawPair1_0.lean; original SHA-256 ea44905280337c51b0dae76e9a312a2c3990f187bca85cabb057b22c1c54b71c; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawPair1_0 : (ThreeBoundMinmaxA.rawAExpr 16 caps records
    (recipe 1 0) (recipe 1 2)).eval profile1≤11659749300103673188588500000000000000000000000000000000000000000000000 := by sorry
