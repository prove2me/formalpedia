-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_25
-- name    : BS2_b3ba934b_Cert_40_RawPair1_25
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T03:36:13.198998+00:00
-- url     : https://prove2.me/theorems/90b976ad-2800-47fc-a197-807ea5f912c8
-- title:
--   Sensitivity separation: Endpoint40RawPair1_25 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_25. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_25.lean; original SHA-256 5fdce64929f0b54ec7a3047848291c974f95ae330b7d845d663caa168587ffd9; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_25 : (rawAExpr 40 caps records (recipe 1 0) (recipe 1 9)).eval profile1≤37858421375922335576410000000000000000000000000000000000000000000000 := by sorry
