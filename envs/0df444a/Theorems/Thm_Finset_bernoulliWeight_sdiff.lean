-- Prove2me | Theorems.Thm_Finset_bernoulliWeight_sdiff
-- name    : Finset.bernoulliWeight_sdiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:59:15.114888+00:00
-- url     : https://prove2.me/theorems/9eaa84d5-1fb2-4aeb-b644-5b7fef29a664
-- title:
--   Finset: bernoulli Weight sdiff
-- statement:
--   Complementing swaps `p` and `1 - p`.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/BernoulliWeights.lean#L109-L111
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/BernoulliWeights.lean#L109-L111

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

theorem Finset.bernoulliWeight_sdiff {A : Finset α} (hA : A ⊆ U) :
    U.bernoulliWeight (1 - p) (U \ A) = U.bernoulliWeight p A := by sorry
