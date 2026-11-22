-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_support_prod_eq_of_additive
-- name    : Formalism.GradedWeylDivisibility.support_prod_eq_of_additive
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:09:11.591063+00:00
-- url     : https://prove2.me/theorems/08802bce-5088-483f-a2b1-6ff47c89b67c
-- title:
--   Graded Weyl Divisibility: support prod eq of additive
-- statement:
--   The Graded Weyl Divisibility construction uses the support prod eq of additive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetdomLemmas.lean#L29-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetdomLemmas.lean#L29-L46

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetdomLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.support_prod_eq_of_additive {σ ι R : Type*} [CommSemiring R] [DecidableEq ι] [DecidableEq σ]
    (F : (σ →₀ ℕ) → ℕ) (hF0 : F 0 = 0) (hFa : ∀ a b, F (a + b) = F a + F b)
    (s : Finset ι) (f : ι → MvPolynomial σ R) (b : ι → ℕ)
    (hb : ∀ i ∈ s, ∀ m ∈ (f i).support, F m = b i) :
    ∀ m ∈ (∏ i ∈ s, f i).support, F m = ∑ i ∈ s, b i := by sorry
