-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_0
-- name    : BS2_b3ba934b_Cert_40_RawPair1_0
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:21:16.396812+00:00
-- url     : https://prove2.me/theorems/19853f96-33a7-48a3-a473-b8efb9e4ebac
-- title:
--   Sensitivity separation: Endpoint40RawPair1_0 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_0. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_0.lean; original SHA-256 2dec0fd5db159d9a9549c4f17ab9f4617662d72d89b42d164e81828f2a0ce657; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_0 : (rawAExpr 40 caps records (recipe 1 0) (recipe 1 2)).eval profile1≤5849894674075950384437030000000000000000000000000000000000000000000000 := by sorry
