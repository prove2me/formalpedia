-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair2_0
-- name    : BS2_b3ba934b_Cert_40_RawPair2_0
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T05:28:14.183841+00:00
-- url     : https://prove2.me/theorems/e33e5c53-4d75-4057-b763-a541dea4fca4
-- title:
--   Sensitivity separation: Endpoint40RawPair2_0 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair2_0. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair2_0.lean; original SHA-256 17a18a02793217556e589f439f43538a5530eddf4a7f869b3a036bb71bdbae57; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair2_0 : (rawAExpr 40 caps records (recipe 2 0) (recipe 2 2)).eval profile2≤439022647791663747058857540000000000000000000000000000000000000000000000 := by sorry
