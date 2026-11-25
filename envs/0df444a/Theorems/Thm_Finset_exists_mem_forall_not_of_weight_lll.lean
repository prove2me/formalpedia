-- Prove2me | Theorems.Thm_Finset_exists_mem_forall_not_of_weight_lll
-- name    : Finset.exists_mem_forall_not_of_weight_lll
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:01:11.249492+00:00
-- url     : https://prove2.me/theorems/5b72f184-62ec-5019-88ae-4832697d834f
-- title:
--   Finset: exists mem forall not of weight lll
-- statement:
--   **The Local Lemma for finite weights, existence form.** Under its hypotheses with all
--   `x i < 1`, some sample point of `Ω` avoids every `E i`.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/LocalLemma.lean#L312-L321
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/LocalLemma.lean#L312-L321

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
variable {β : Type*} (E : ι → β → Prop) [∀ i, DecidablePred (E i)]
variable {E}
variable {Ω : Finset β} {w : β → ℝ}

theorem Finset.exists_mem_forall_not_of_weight_lll (hw0 : ∀ a ∈ Ω, 0 ≤ w a)
    (hw1 : ∑ a ∈ Ω, w a = 1) {I : Finset ι} {Γ : ι → Finset ι} (hL : LopsidedWeights Ω w I E Γ)
    {x : ι → ℝ} (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hp : ∀ i ∈ I, Ω.weightProb w (E i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) :
    ∃ a ∈ Ω, ∀ i ∈ I, ¬E i a := by sorry
