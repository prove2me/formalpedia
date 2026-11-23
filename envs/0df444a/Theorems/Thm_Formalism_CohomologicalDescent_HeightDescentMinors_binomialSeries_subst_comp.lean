-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_binomialSeries_subst_comp
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.binomialSeries_subst_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:30.895005+00:00
-- url     : https://prove2.me/theorems/76e215f9-0407-4578-b2ab-906cab00803a
-- title:
--   Height Descent Minors: binomial Series subst comp
-- statement:
--   The Height Descent Minors construction uses the binomial Series subst comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L66-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L66-L94

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
attribute [local instance] BinomialRing.toIsAddTorsionFree

theorem Formalism.CohomologicalDescent.HeightDescentMinors.binomialSeries_subst_comp (d e : R) :
    (binomialSeries R d).subst (binomialSeries R e - 1 : R⟦X⟧) = binomialSeries R (d * e) := by sorry
