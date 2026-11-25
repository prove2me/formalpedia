-- Prove2me | Theorems.Thm_Finset_bernoulliProb_le_one
-- name    : Finset.bernoulliProb_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:01:27.690725+00:00
-- url     : https://prove2.me/theorems/4bae58f9-16c5-51a2-b7b4-a5fe02778479
-- title:
--   Finset: bernoulli Prob le one
-- statement:
--   For `0 ≤ p ≤ 1` probabilities are at most `1`.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/BernoulliWeights.lean#L97-L101
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/BernoulliWeights.lean#L97-L101

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

theorem Finset.bernoulliProb_le_one (h0 : 0 ≤ p) (h1 : p ≤ 1) (P : Finset α → Prop) [DecidablePred P] :
    U.bernoulliProb p P ≤ 1 := by sorry
