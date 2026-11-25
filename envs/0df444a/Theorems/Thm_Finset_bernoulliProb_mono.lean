-- Prove2me | Theorems.Thm_Finset_bernoulliProb_mono
-- name    : Finset.bernoulliProb_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:02:02.626209+00:00
-- url     : https://prove2.me/theorems/1b9d658d-ec23-4cdf-b5ac-7d6f22b38c4b
-- title:
--   Finset: bernoulli Prob mono
-- statement:
--   A weaker event is at least as likely.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/LocalLemma.lean#L81-L84
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/LocalLemma.lean#L81-L84

module
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Definitions.Def_ProbabilisticMethod_LocalLemma
set_option autoImplicit true
@[expose] public section
public section
open Finset Real
open Finset
variable {α ι : Type*} [DecidableEq α] {U : Finset α} {p : ℝ}
variable (U p)
variable {U p}

theorem Finset.bernoulliProb_mono (h0 : 0 ≤ p) (h1 : p ≤ 1) {P Q : Finset α → Prop} [DecidablePred P]
    [DecidablePred Q] (h : ∀ A, P A → Q A) : U.bernoulliProb p P ≤ U.bernoulliProb p Q := by sorry
