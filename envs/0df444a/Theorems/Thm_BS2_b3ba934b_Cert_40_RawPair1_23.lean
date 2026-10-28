-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_23
-- name    : BS2_b3ba934b_Cert_40_RawPair1_23
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T03:28:29.769993+00:00
-- url     : https://prove2.me/theorems/db78cbbf-7ace-46df-be54-d23de43f4421
-- title:
--   Sensitivity separation: Endpoint40RawPair1_23 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_23. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_23.lean; original SHA-256 80618970c5b589e649c868cdf162b5df63badefaa40def400c420f49a9d25844; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_23 : (rawAExpr 40 caps records (recipe 1 5) (recipe 1 7)).eval profile1≤45307068002858374123276540000000000000000000000000000000000000000000000 := by sorry
