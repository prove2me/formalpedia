-- Prove2me | Theorems.Thm_Finset_weightProb_mono
-- name    : Finset.weightProb_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:01:01.416791+00:00
-- url     : https://prove2.me/theorems/f66caa7a-c787-5dfe-861b-336eed0553bd
-- title:
--   Finset: weight Prob mono
-- statement:
--   For nonnegative weights, a weaker event is at least as likely.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/LocalLemma.lean#L112-L115
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/LocalLemma.lean#L112-L115

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
variable {β : Type*}
variable {Ω : Finset β} {w : β → ℝ}

theorem Finset.weightProb_mono (hw0 : ∀ a ∈ Ω, 0 ≤ w a) {P Q : β → Prop} [DecidablePred P]
    [DecidablePred Q] (h : ∀ a, P a → Q a) : Ω.weightProb w P ≤ Ω.weightProb w Q := by sorry
