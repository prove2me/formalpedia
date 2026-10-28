-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair2_2
-- name    : BS2_b3ba934b_Cert_40_RawPair2_2
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T05:48:18.943986+00:00
-- url     : https://prove2.me/theorems/2ad5e1b5-89d5-4798-b11c-d28a7da28d53
-- title:
--   Sensitivity separation: Endpoint40RawPair2_2 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair2_2. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair2_2.lean; original SHA-256 e245d3dd0ab83b0039bada2fb3e344d8aeda10772f590a4e1a1729a56d006ef5; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair2_2 : (rawAExpr 40 caps records (recipe 2 2) (recipe 2 2)).eval profile2≤10509878689536842271677007430000000000000000000000000000000000000000000000 := by sorry
