-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_subst_powerSeries
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.map_subst_powerSeries
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:28:28.363919+00:00
-- url     : https://prove2.me/theorems/e87ddb8f-65b1-464e-a077-1c577d87ff4c
-- title:
--   Height Descent Minors: map subst power Series
-- statement:
--   The Height Descent Minors construction uses the map subst power Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L423-L430
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L423-L430

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.map_subst_powerSeries {R S : Type} [CommRing R] [CommRing S] (h : R →+* S) {a : R⟦X⟧}
    (ha : HasSubst a) (f : R⟦X⟧) :
    PowerSeries.map h (f.subst a) = (PowerSeries.map h f).subst (PowerSeries.map h a) := by sorry
