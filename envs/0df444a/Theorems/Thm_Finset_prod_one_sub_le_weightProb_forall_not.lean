-- Prove2me | Theorems.Thm_Finset_prod_one_sub_le_weightProb_forall_not
-- name    : Finset.prod_one_sub_le_weightProb_forall_not
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:00:28.060868+00:00
-- url     : https://prove2.me/theorems/9c9c07e6-83b7-4fbd-8d99-72a1411c7748
-- title:
--   Finset: prod one sub le weight Prob forall not
-- statement:
--   **The Lovász Local Lemma** (asymmetric, lopsided form) for any finite probability: weights
--   `w ≥ 0` on a finite sample set `Ω` with total `1`. Under the lopsided hypothesis, if
--   `P(E i) ≤ x i ∏ j ∈ Γ i, (1 - x j)` with `0 ≤ x ≤ 1`, then no `E i` occurs with probability at
--   least `∏ i ∈ I, (1 - x i)`.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/LocalLemma.lean#L286-L308
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/LocalLemma.lean#L286-L308

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

theorem Finset.prod_one_sub_le_weightProb_forall_not (hw0 : ∀ a ∈ Ω, 0 ≤ w a)
    (hw1 : ∑ a ∈ Ω, w a = 1) {I : Finset ι} {Γ : ι → Finset ι} (hL : LopsidedWeights Ω w I E Γ)
    {x : ι → ℝ} (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1)
    (hp : ∀ i ∈ I, Ω.weightProb w (E i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) :
    ∏ i ∈ I, (1 - x i) ≤ Ω.weightProb w (Avoids E I) := by sorry
