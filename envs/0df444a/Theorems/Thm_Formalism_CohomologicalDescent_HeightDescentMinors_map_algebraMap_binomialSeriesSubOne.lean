-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_algebraMap_binomialSeriesSubOne
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.map_algebraMap_binomialSeriesSubOne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:03:43.465796+00:00
-- url     : https://prove2.me/theorems/d343dcff-709c-4c08-98d2-a16a74d33d1d
-- title:
--   Height Descent Minors: map algebra Map binomial Series Sub One
-- statement:
--   The Height Descent Minors construction uses the map algebra Map binomial Series Sub One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L197-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L197-L199

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
variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]

theorem Formalism.CohomologicalDescent.HeightDescentMinors.map_algebraMap_binomialSeriesSubOne (c : ℤ_[l]) :
    PowerSeries.map (algebraMap ℤ_[l] O) (br l ℤ_[l] c) = br l O c := by sorry
