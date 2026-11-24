-- Prove2me | Theorems.Thm_FairChores_bag_aux
-- name    : FairChores.bag_aux
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:18:25.694604+00:00
-- url     : https://prove2.me/theorems/715a1b87-fa67-45d9-aa7b-33f66dfeeb5e
-- title:
--   Fair Chores: bag aux
-- statement:
--   The `while` loop of Algorithm 13, by induction on the number of available chores.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresBagLemma.lean#L89-L168
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresBagLemma.lean#L89-L168

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresBagLemma
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable (c : Fin n → T → ℝ) (p : T → ℝ) (mu : Fin n → ℝ)
variable {c p mu}
omit [Fintype T]

theorem FairChores.bag_aux (hc : ∀ i t, 0 ≤ c i t) (hp : ∀ t, 0 ≤ p t) (hmu : ∀ i, 0 < mu i)
    (A : Finset (Fin n)) (R : Finset T) :
    ∀ (m : ℕ) (X Psi : Finset T), X ⊆ R → Psi ⊆ R → Disjoint X Psi →
      (R \ (X ∪ Psi)).card ≤ m →
      (∀ j ∈ A, mu j ≤ cbarSum (c j) p X ∨ ∀ t ∈ Psi, mu j < cbar (c j) p t) →
      (X = ∅ → ∀ t ∈ Psi, ∀ j ∈ A, 2 * mu j < cbar (c j) p t) →
      (∃ j ∈ A, cbarSum (c j) p X < mu j) →
      BagGoal c p mu A R := by sorry
