-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lccomp_sum_components
-- name    : Formalism.GradedWeylDivisibility.lccomp_sum_components
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:00.059407+00:00
-- url     : https://prove2.me/theorems/a75256fd-3f69-47f2-948a-05a76179db0b
-- title:
--   Graded Weyl Divisibility: lccomp sum components
-- statement:
--   The Graded Weyl Divisibility construction uses the lccomp sum components property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCcompLemmas.lean#L60-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCcompLemmas.lean#L60-L72

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCcompLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.lccomp_sum_components {R : Type*} [CommRing R] {σ M : Type*} [AddCommMonoid M] [DecidableEq M]
    (w : σ → M) (f : MvPolynomial σ R) (T : Finset M)
    (hT : ∀ d ∈ f.support, Finsupp.weight w d ∈ T) :
    f = ∑ ω' ∈ T, weightedHomogeneousComponent w ω' f := by sorry
