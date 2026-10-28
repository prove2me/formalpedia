-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawOther3
-- name    : BS2_b3ba934b_Cert_40_RawOther3
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T07:27:17.746589+00:00
-- url     : https://prove2.me/theorems/b988e5a9-0bdd-4e02-aac1-4f765f931422
-- title:
--   Sensitivity separation: Endpoint40RawOther3 ordinary_and_transfer checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawOther3. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther3.lean; original SHA-256 688770f8c78517daf4ca8613d7835919a93003fe068a5e5ce8edd6224aa521eb; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawOther3 :
    (∀ i j : Fin 40, i≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    (rawAExpr 40 caps records (recipe 3 i) (recipe 3 j)).eval profile3≤rawProfile3 (.a i j)) ∧
    (∀ (ha : ∀ i j : Fin 40, i≤j →
      (rawAExpr 40 caps records (recipe 3 i) (recipe 3 j)).eval profile3≤rawProfile3 (.a i j)),
∀ coord : Coord 40, valid coord → raw 3 profile3 coord≤rawProfile3 coord) := by sorry
