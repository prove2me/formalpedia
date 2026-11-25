-- Prove2me | Theorems.Thm_Finset_bernoulliProb_superset
-- name    : Finset.bernoulliProb_superset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:59:17.022593+00:00
-- url     : https://prove2.me/theorems/eee3ccb4-5e20-42ca-bb56-a393f26b4c39
-- title:
--   Finset: bernoulli Prob superset
-- statement:
--   **`P(F ⊆ A) = p ^ |F|`.**
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/BernoulliWeights.lean#L114-L136
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/BernoulliWeights.lean#L114-L136

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

theorem Finset.bernoulliProb_superset {F : Finset α} (hF : F ⊆ U) :
    U.bernoulliProb p (F ⊆ ·) = p ^ #F := by sorry
