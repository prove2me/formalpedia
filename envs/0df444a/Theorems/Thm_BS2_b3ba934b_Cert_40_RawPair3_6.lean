-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawPair3_6
-- name    : BS2_b3ba934b_Cert_40_RawPair3_6
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T07:01:36.616313+00:00
-- url     : https://prove2.me/theorems/b38e0088-e606-43e1-8498-dc6e7064512c
-- title:
--   Sensitivity separation: Endpoint40RawPair3_6 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawPair3_6. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair3_6.lean; original SHA-256 92aa7a31993cb413cd027c793889c9a36ea97d7e53f1d0c3eafd240e5d4aa31f; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawPair3_6 : (rawAExpr 40 caps records (recipe 3 2) (recipe 3 4)).eval profile3≤25006000113424645102729645880000000000000000000000000000000000000000000000 := by sorry
