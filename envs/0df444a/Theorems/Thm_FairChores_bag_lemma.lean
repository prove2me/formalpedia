-- Prove2me | Theorems.Thm_FairChores_bag_lemma
-- name    : FairChores.bag_lemma
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:18:30.593698+00:00
-- url     : https://prove2.me/theorems/7442cee9-4f15-4767-9e0c-27e57165cae2
-- title:
--   Fair Chores: bag lemma
-- statement:
--   **The bag-filling lemma.**  For any nonempty set `A` of active agents and any set `R` of
--   available chores, either all remaining chores are very expensive for all active agents, or a
--   nonempty bag can be handed to an active agent at cost at most twice its threshold, in such a
--   way that every other active agent either finds the bag costly enough or finds every remaining
--   chore expensive.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresBagLemma.lean#L176-L183
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresBagLemma.lean#L176-L183

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

theorem FairChores.bag_lemma (hc : ∀ i t, 0 ≤ c i t) (hp : ∀ t, 0 ≤ p t) (hmu : ∀ i, 0 < mu i)
    {A : Finset (Fin n)} (hA : A.Nonempty) (R : Finset T) :
    BagGoal c p mu A R := by sorry
