-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_binomialSeries_subst_sub_one_eq_mul
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.binomialSeries_subst_sub_one_eq_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:42.11065+00:00
-- url     : https://prove2.me/theorems/f7f4998e-09cf-41c3-879c-b1cd18dd06c3
-- title:
--   Height Descent Minors: binomial Series subst sub one eq mul
-- statement:
--   The Height Descent Minors construction uses the binomial Series subst sub one eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L104-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L104-L115

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable {R : Type*} [CommRing R]
variable [BinomialRing R]

theorem Formalism.CohomologicalDescent.HeightDescentMinors.binomialSeries_subst_sub_one_eq_mul {A : Type*} [CommRing A] [Algebra R A] (d e : R) :
    (binomialSeries A d).subst (binomialSeries A e - 1 : A⟦X⟧) = binomialSeries A (d * e) := by sorry
