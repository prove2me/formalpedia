-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair2_2
-- name    : BS2_b3ba934b_Cert_16_RawPair2_2
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:28:50.139991+00:00
-- url     : https://prove2.me/theorems/ccede7a7-d231-41ca-adb7-d932703b9e98
-- title:
--   Sensitivity separation: Endpoint16RawPair2_2 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawPair2_2. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawPair2_2.lean; original SHA-256 079404661851390e958d4d4fb4aa173892f29094d0d202d756d7334ec34ba23d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawPair2_2 : (ThreeBoundMinmaxA.rawAExpr 16 caps records
    (recipe 2 2) (recipe 2 2)).eval profile2≤14410105262606791464357289260000000000000000000000000000000000000000000000 := by sorry
