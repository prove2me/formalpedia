-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_38
-- name    : BS2_b3ba934b_Cert_40_RawPair1_38
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T04:21:49.252473+00:00
-- url     : https://prove2.me/theorems/75e88397-daf9-4bcd-8fa4-ff2e54b43b72
-- title:
--   Sensitivity separation: Endpoint40RawPair1_38 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_38. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_38.lean; original SHA-256 80909effb0183f8b9c77f0d4fe17b27c7666436aa141f6f59ecf0fbbaa568b1a; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_38 : (rawAExpr 40 caps records (recipe 1 5) (recipe 1 10)).eval profile1≤45306527546439468734521540000000000000000000000000000000000000000000000 := by sorry
