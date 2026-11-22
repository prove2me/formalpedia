-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_unit_mul_X_pow
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.hasSubst_unit_mul_X_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:19:33.59034+00:00
-- url     : https://prove2.me/theorems/7f7f4e2d-a27b-48c5-9c82-82635edcd495
-- title:
--   Height Descent Minors: has Subst unit mul X pow
-- statement:
--   The Height Descent Minors construction uses the has Subst unit mul X pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L747-L750
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L747-L750

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.hasSubst_unit_mul_X_pow (n : ℕ) (hn : 0 < n) (w : (R⟦X⟧)ˣ) : HasSubst ((w : R⟦X⟧) * X ^ n) := by sorry
