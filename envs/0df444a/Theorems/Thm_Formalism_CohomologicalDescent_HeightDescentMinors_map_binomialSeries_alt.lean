-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_binomialSeries_alt
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.map_binomialSeries_alt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:29:06.949955+00:00
-- url     : https://prove2.me/theorems/6fc42f48-2132-4077-bbdd-fc99e525894d
-- title:
--   Height Descent Minors: map binomial Series alt
-- statement:
--   The Height Descent Minors construction uses the map binomial Series alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L96-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L96-L102

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.map_binomialSeries_alt {A : Type*} [CommRing A] [Algebra R A] (c : R) :
    PowerSeries.map (algebraMap R A) (binomialSeries R c) = binomialSeries A c := by sorry
