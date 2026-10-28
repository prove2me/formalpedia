-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_27
-- name    : BS2_b3ba934b_Cert_40_RawPair1_27
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T03:43:14.984987+00:00
-- url     : https://prove2.me/theorems/3996684b-c010-426b-8f75-d3c3b4d36303
-- title:
--   Sensitivity separation: Endpoint40RawPair1_27 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_27. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_27.lean; original SHA-256 08a3249be95ee756106c9598bd0ef5e73ec7a3b8220bb9aab1babea29c90f168; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_27 : (rawAExpr 40 caps records (recipe 1 2) (recipe 1 9)).eval profile1≤37858421375922335576410000000000000000000000000000000000000000000000 := by sorry
