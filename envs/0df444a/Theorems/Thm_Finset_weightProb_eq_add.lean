-- Prove2me | Theorems.Thm_Finset_weightProb_eq_add
-- name    : Finset.weightProb_eq_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:01:06.679742+00:00
-- url     : https://prove2.me/theorems/357606a6-9214-4275-8c67-b9d0632ad64e
-- title:
--   Finset: weight Prob eq add
-- statement:
--   Splitting an event along another: `P(P) = P(P ∧ Q) + P(P ∧ ¬Q)`.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/LocalLemma.lean#L118-L123
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/LocalLemma.lean#L118-L123

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

theorem Finset.weightProb_eq_add (Ω : Finset β) (w : β → ℝ) (P Q : β → Prop) [DecidablePred P]
    [DecidablePred Q] :
    Ω.weightProb w P =
      Ω.weightProb w (fun a => P a ∧ Q a) + Ω.weightProb w (fun a => P a ∧ ¬Q a) := by sorry
