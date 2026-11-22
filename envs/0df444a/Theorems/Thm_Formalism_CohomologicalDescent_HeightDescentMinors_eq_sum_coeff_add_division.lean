-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_eq_sum_coeff_add_division
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.eq_sum_coeff_add_division
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:28:44.458061+00:00
-- url     : https://prove2.me/theorems/6daa8e60-5e72-4edc-8fde-c03f00116195
-- title:
--   Height Descent Minors: eq sum coeff add division
-- statement:
--   The Height Descent Minors construction uses the eq sum coeff add division property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L765-L790
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L765-L790

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.eq_sum_coeff_add_division (n : ℕ) (w : (R⟦X⟧)ˣ) (f : R⟦X⟧) :
    f = ∑ j : Fin n, C (coeff (j : ℕ) f) * X ^ (j : ℕ) + (w : R⟦X⟧) * X ^ n * divQuotient n w f := by sorry
