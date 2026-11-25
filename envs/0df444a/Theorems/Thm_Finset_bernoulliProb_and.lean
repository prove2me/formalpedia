-- Prove2me | Theorems.Thm_Finset_bernoulliProb_and
-- name    : Finset.bernoulliProb_and
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:00:35.204111+00:00
-- url     : https://prove2.me/theorems/6eb2600b-4df7-47dc-bf42-dbcea0d66946
-- title:
--   Finset: bernoulli Prob and
-- statement:
--   **Independence.** Events depending on disjoint coordinate sets `T, T' ⊆ U` are independent:
--   `P(P ∧ Q) = P(P) P(Q)`.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/BernoulliWeights.lean#L210-L252
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/BernoulliWeights.lean#L210-L252

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

theorem Finset.bernoulliProb_and {T T' : Finset α} (hT : T ⊆ U) (hT' : T' ⊆ U) (hTT' : Disjoint T T')
    {P Q : Finset α → Prop} [DecidablePred P] [DecidablePred Q] (hP : DependsOnCoords P T)
    (hQ : DependsOnCoords Q T') :
    U.bernoulliProb p (fun A => P A ∧ Q A) = U.bernoulliProb p P * U.bernoulliProb p Q := by sorry
