-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawOther2
-- name    : BS2_b3ba934b_Cert_40_RawOther2
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T06:26:26.997167+00:00
-- url     : https://prove2.me/theorems/9592a5a3-e535-4760-a0fc-42891707f3bd
-- title:
--   Sensitivity separation: Endpoint40RawOther2 ordinary_and_transfer checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawOther2. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther2.lean; original SHA-256 6522282cdeb9874123a393494ec676ca3c96e1cf3653d9d2b1a0c2a5503dc3cf; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawOther2 :
    (∀ i j : Fin 40, i≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    (rawAExpr 40 caps records (recipe 2 i) (recipe 2 j)).eval profile2≤rawProfile2 (.a i j)) ∧
    (∀ (ha : ∀ i j : Fin 40, i≤j →
      (rawAExpr 40 caps records (recipe 2 i) (recipe 2 j)).eval profile2≤rawProfile2 (.a i j)),
∀ coord : Coord 40, valid coord → raw 2 profile2 coord≤rawProfile2 coord) := by sorry
