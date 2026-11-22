-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_coeff_eq_zero_of_subst_invariant
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.coeff_eq_zero_of_subst_invariant
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:26:56.758973+00:00
-- url     : https://prove2.me/theorems/43b7cf00-10d0-40bf-9e8f-dbdc19459479
-- title:
--   Height Descent Minors: coeff eq zero of subst invariant
-- statement:
--   The Height Descent Minors construction uses the coeff eq zero of subst invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L926-L936
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L926-L936

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.coeff_eq_zero_of_subst_invariant (s f : R⟦X⟧) (n : ℕ) (hinv : f.subst (X * s) = f)
    (hu : ∀ j, 0 < j → j < n → IsUnit (constantCoeff s ^ j - 1)) :
    ∀ j, 0 < j → j < n → coeff j f = 0 := by sorry
