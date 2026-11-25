-- Prove2me | Theorems.Thm_Finset_expectation_card_filter
-- name    : Finset.expectation_card_filter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:59:22.470833+00:00
-- url     : https://prove2.me/theorems/2890af61-2a71-42e7-a51f-5a82cbe3956c
-- title:
--   Finset: expectation card filter
-- statement:
--   **Linearity of expectation for counts.** The expected number of the events `E i`, `i ∈ I`,
--   that occur is the sum of their probabilities.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/BernoulliWeights.lean#L280-L286
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/BernoulliWeights.lean#L280-L286

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

theorem Finset.expectation_card_filter {ι : Type*} (I : Finset ι) (E : ι → Finset α → Prop)
    [∀ i, DecidablePred (E i)] :
    ∑ B ∈ U.powerset, U.bernoulliWeight p B * (#{i ∈ I | E i B} : ℝ) =
      ∑ i ∈ I, U.bernoulliProb p (E i) := by sorry
