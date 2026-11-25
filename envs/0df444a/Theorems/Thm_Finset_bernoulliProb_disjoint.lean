-- Prove2me | Theorems.Thm_Finset_bernoulliProb_disjoint
-- name    : Finset.bernoulliProb_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:59:40.385882+00:00
-- url     : https://prove2.me/theorems/e58ab8d0-795a-4733-92b8-b54bc567cade
-- title:
--   Finset: bernoulli Prob disjoint
-- statement:
--   **`P(A ∩ F = ∅) = (1 - p) ^ |F|`.**
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/BernoulliWeights.lean#L139-L152
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/BernoulliWeights.lean#L139-L152

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

theorem Finset.bernoulliProb_disjoint {F : Finset α} (hF : F ⊆ U) :
    U.bernoulliProb p (Disjoint · F) = (1 - p) ^ #F := by sorry
