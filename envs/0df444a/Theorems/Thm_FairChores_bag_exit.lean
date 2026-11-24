-- Prove2me | Theorems.Thm_FairChores_bag_exit
-- name    : FairChores.bag_exit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:18:25.649083+00:00
-- url     : https://prove2.me/theorems/2e23ac71-889a-4019-8220-628779012f03
-- title:
--   Fair Chores: bag exit
-- statement:
--   The exit case of the `while` loop: no chore is available any more.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresBagLemma.lean#L51-L85
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresBagLemma.lean#L51-L85

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

theorem FairChores.bag_exit (hmu : ∀ i, 0 < mu i) {A : Finset (Fin n)} {R X Psi : Finset T}
    (hX : X ⊆ R) (hPsi : Psi ⊆ R) (hdisj : Disjoint X Psi)
    (hempty : R \ (X ∪ Psi) = ∅)
    (hP : ∀ j ∈ A, mu j ≤ cbarSum (c j) p X ∨ ∀ t ∈ Psi, mu j < cbar (c j) p t)
    (hQ : X = ∅ → ∀ t ∈ Psi, ∀ j ∈ A, 2 * mu j < cbar (c j) p t)
    (hU : ∃ j ∈ A, cbarSum (c j) p X < mu j) :
    BagGoal c p mu A R := by sorry
