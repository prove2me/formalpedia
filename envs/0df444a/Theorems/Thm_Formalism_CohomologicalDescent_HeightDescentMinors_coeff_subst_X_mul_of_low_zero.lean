-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_coeff_subst_X_mul_of_low_zero
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.coeff_subst_X_mul_of_low_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:38.398944+00:00
-- url     : https://prove2.me/theorems/2d31ea3b-e97a-4371-bf3a-cd6b7d724b40
-- title:
--   Height Descent Minors: coeff subst X mul of low zero
-- statement:
--   The Height Descent Minors construction uses the coeff subst X mul of low zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L907-L924
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L907-L924

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
variable {R : Type} [CommRing R]

theorem Formalism.CohomologicalDescent.HeightDescentMinors.coeff_subst_X_mul_of_low_zero (s f : R⟦X⟧) (j : ℕ) (hj : 0 < j)
    (h0 : ∀ i, 0 < i → i < j → coeff i f = 0) :
    coeff j (f.subst (X * s)) = coeff j f * constantCoeff s ^ j := by sorry
