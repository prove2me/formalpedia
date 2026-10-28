-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_30
-- name    : BS2_b3ba934b_Cert_40_RawPair1_30
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T03:52:30.672998+00:00
-- url     : https://prove2.me/theorems/366f68e8-68ac-4638-8db9-bb9f1c2db069
-- title:
--   Sensitivity separation: Endpoint40RawPair1_30 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_30. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_30.lean; original SHA-256 f1c838b192ae3afd63a332d74c6c0a4eaec386ecf6aecc9063049a4220a19be8; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_30 : (rawAExpr 40 caps records (recipe 1 5) (recipe 1 9)).eval profile1≤45306527546439468734521540000000000000000000000000000000000000000000000 := by sorry
