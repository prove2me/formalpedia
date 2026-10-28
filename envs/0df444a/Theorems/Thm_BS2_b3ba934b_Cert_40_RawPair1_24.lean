-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_24
-- name    : BS2_b3ba934b_Cert_40_RawPair1_24
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T03:31:49.299668+00:00
-- url     : https://prove2.me/theorems/04123960-1bff-49c6-91da-92c33d0a8a3d
-- title:
--   Sensitivity separation: Endpoint40RawPair1_24 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_24. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_24.lean; original SHA-256 d9110678db13cb2a4dda98a8c4f46b0425b28512840cbafba8e67671c5e45eb2; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_24 : (rawAExpr 40 caps records (recipe 1 7) (recipe 1 7)).eval profile1≤45307068002858374123276540000000000000000000000000000000000000000000000 := by sorry
