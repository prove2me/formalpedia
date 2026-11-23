-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_subst_X_eq_self
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.subst_X_eq_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:39.225271+00:00
-- url     : https://prove2.me/theorems/956476e7-c58e-4311-9d55-17b67415aef6
-- title:
--   Height Descent Minors: subst X eq self
-- statement:
--   The Height Descent Minors construction uses the subst X eq self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L121-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L121-L121

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.subst_X_eq_self {R : Type*} [CommRing R] (f : R⟦X⟧) : f.subst (X : R⟦X⟧) = f := by sorry
