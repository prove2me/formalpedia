-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lccomp_degreeOf_component_le
-- name    : Formalism.GradedWeylDivisibility.lccomp_degreeOf_component_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:46.47307+00:00
-- url     : https://prove2.me/theorems/ca8db333-d8af-4903-b539-56b7f45c6987
-- title:
--   Graded Weyl Divisibility: lccomp degree Of component le
-- statement:
--   The Graded Weyl Divisibility construction uses the lccomp degree Of component le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCcompLemmas.lean#L130-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCcompLemmas.lean#L130-L140

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

theorem Formalism.GradedWeylDivisibility.lccomp_degreeOf_component_le {R : Type*} [CommRing R] {σ M : Type*} [AddCommMonoid M]
    (w : σ → M) (ω : M) (p : MvPolynomial σ R) (i : σ) :
    degreeOf i (weightedHomogeneousComponent w ω p) ≤ degreeOf i p := by sorry
