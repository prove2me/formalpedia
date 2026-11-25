-- Prove2me | Theorems.Thm_Finset_sum_bernoulliWeight
-- name    : Finset.sum_bernoulliWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:59:09.711351+00:00
-- url     : https://prove2.me/theorems/dc360ec9-f897-42ee-8060-fc8305590f96
-- title:
--   Finset: sum bernoulli Weight
-- statement:
--   The weights sum to `1`.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/BernoulliWeights.lean#L89-L94
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/BernoulliWeights.lean#L89-L94

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
variable (U p)

theorem Finset.sum_bernoulliWeight : ∑ A ∈ U.powerset, U.bernoulliWeight p A = 1 := by sorry
