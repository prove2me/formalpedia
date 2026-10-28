-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair1_3
-- name    : BS2_b3ba934b_Cert_40_RawPair1_3
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:33:49.049392+00:00
-- url     : https://prove2.me/theorems/510cd0dd-4a89-4be2-a6d7-7713c9d96eda
-- title:
--   Sensitivity separation: Endpoint40RawPair1_3 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair1_3. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair1_3.lean; original SHA-256 d8636d8d4fe18c74ea60bfb2310cf348ddc4993417fe21d8ab882529b4dbadc3; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair1_3 : (rawAExpr 40 caps records (recipe 1 0) (recipe 1 3)).eval profile1≤5840625979435819554426000000000000000000000000000000000000000000000000 := by sorry
