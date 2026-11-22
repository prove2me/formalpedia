-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_cancel_unit_mul_X_pow
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.cancel_unit_mul_X_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:26:39.632121+00:00
-- url     : https://prove2.me/theorems/6cfb19c3-2635-4f0e-8524-41ea83bb368e
-- title:
--   Height Descent Minors: cancel unit mul X pow
-- statement:
--   The Height Descent Minors construction uses the cancel unit mul X pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L752-L760
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L752-L760

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.cancel_unit_mul_X_pow (n : ℕ) (w : (R⟦X⟧)ˣ) {a b : R⟦X⟧}
    (h : (w : R⟦X⟧) * X ^ n * a = (w : R⟦X⟧) * X ^ n * b) : a = b := by sorry
