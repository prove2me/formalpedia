-- Prove2me | Theorems.Thm_Finset_prod_one_sub_le_bernoulliProb_forall_not
-- name    : Finset.prod_one_sub_le_bernoulliProb_forall_not
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:02:17.69481+00:00
-- url     : https://prove2.me/theorems/3479d383-9ec4-5346-beb5-e59b98851dcb
-- title:
--   Finset: prod one sub le bernoulli Prob forall not
-- statement:
--   **The Lovász Local Lemma** on the `p`-biased cube (asymmetric, lopsided form): the case
--   `Ω = U.powerset`, `w = U.bernoulliWeight p` of `prod_one_sub_le_weightProb_forall_not`.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/LocalLemma.lean#L329-L335
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/LocalLemma.lean#L329-L335

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

theorem Finset.prod_one_sub_le_bernoulliProb_forall_not (h0 : 0 ≤ p) (h1 : p ≤ 1) {I : Finset ι}
    {Γ : ι → Finset ι} (hL : Lopsided U p I E Γ) {x : ι → ℝ} (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∀ i, x i ≤ 1)
    (hp : ∀ i ∈ I, U.bernoulliProb p (E i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) :
    ∏ i ∈ I, (1 - x i) ≤ U.bernoulliProb p (Avoids E I) := by sorry
