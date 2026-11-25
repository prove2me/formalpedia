-- Prove2me | Theorems.Thm_Finset_bernoulliProb_congr
-- name    : Finset.bernoulliProb_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:01:29.396257+00:00
-- url     : https://prove2.me/theorems/097adc6a-6958-4a7e-a2c4-10ed55814672
-- title:
--   Finset: bernoulli Prob congr
-- statement:
--   Events that agree on the subsets of `U` have the same probability.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/BernoulliWeights.lean#L104-L106
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/BernoulliWeights.lean#L104-L106

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

theorem Finset.bernoulliProb_congr {P Q : Finset α → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ A ⊆ U, P A ↔ Q A) : U.bernoulliProb p P = U.bernoulliProb p Q := by sorry
