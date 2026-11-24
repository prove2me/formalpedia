-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_binomialSeriesSubOne_algebraMap
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.map_binomialSeriesSubOne_algebraMap
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:37:28.247854+00:00
-- url     : https://prove2.me/theorems/82d10efd-a14f-4bdb-a8c8-2d28f19dd2b6
-- title:
--   Height Descent Minors: map binomial Series Sub One algebra Map
-- statement:
--   The Height Descent Minors construction uses the map binomial Series Sub One algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L477-L478
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L477-L478

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.map_binomialSeriesSubOne_algebraMap (c : ℤ_[l]) :
    PowerSeries.map (algebraMap ℤ_[l] O) (br l ℤ_[l] c) = br l O c := by sorry
