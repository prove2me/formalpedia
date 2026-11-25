-- Prove2me | Theorems.Thm_Finset_exists_forall_not_of_sum_bernoulliProb_lt
-- name    : Finset.exists_forall_not_of_sum_bernoulliProb_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:01:41.538421+00:00
-- url     : https://prove2.me/theorems/ad5ffd7a-705e-422c-85e8-6db279a3609f
-- title:
--   Finset: exists forall not of sum bernoulli Prob lt
-- statement:
--   **The union bound.** If the probabilities of the bad events `E i`, `i ∈ I`, add up to less
--   than `1`, then some `A ⊆ U` avoids all of them.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/BernoulliWeights.lean#L290-L299
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/BernoulliWeights.lean#L290-L299

module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights
set_option autoImplicit true
@[expose] public section
public section
open Finset
open Finset
variable {α : Type*} [DecidableEq α] (U : Finset α) (p : ℝ)
variable {U p}

theorem Finset.exists_forall_not_of_sum_bernoulliProb_lt {ι : Type*} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (I : Finset ι) (E : ι → Finset α → Prop) [∀ i, DecidablePred (E i)]
    (h : ∑ i ∈ I, U.bernoulliProb p (E i) < 1) :
    ∃ A ∈ U.powerset, ∀ i ∈ I, ¬E i A := by sorry
