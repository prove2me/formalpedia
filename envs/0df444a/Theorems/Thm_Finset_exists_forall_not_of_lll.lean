-- Prove2me | Theorems.Thm_Finset_exists_forall_not_of_lll
-- name    : Finset.exists_forall_not_of_lll
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:01:18.741252+00:00
-- url     : https://prove2.me/theorems/11a0020b-d15e-49df-8418-ef07d7cb46fd
-- title:
--   Finset: exists forall not of lll
-- statement:
--   **The Local Lemma, existence form.** Under its hypotheses with all `x i < 1`, some `A ⊆ U`
--   avoids every `E i`.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/LocalLemma.lean#L339-L344
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/LocalLemma.lean#L339-L344

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
variable {E : ι → Finset α → Prop} [∀ i, DecidablePred (E i)]

theorem Finset.exists_forall_not_of_lll (h0 : 0 ≤ p) (h1 : p ≤ 1) {I : Finset ι} {Γ : ι → Finset ι}
    (hL : Lopsided U p I E Γ) {x : ι → ℝ} (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hp : ∀ i ∈ I, U.bernoulliProb p (E i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) :
    ∃ A ∈ U.powerset, ∀ i ∈ I, ¬E i A := by sorry
