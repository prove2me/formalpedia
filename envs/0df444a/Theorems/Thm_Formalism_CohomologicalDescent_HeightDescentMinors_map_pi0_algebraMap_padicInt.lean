-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_pi0_algebraMap_padicInt
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.map_pi0_algebraMap_padicInt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:12.994793+00:00
-- url     : https://prove2.me/theorems/d7b52011-c3c4-46c4-99f3-32d7297b27be
-- title:
--   Height Descent Minors: map pi0 algebra Map padic Int
-- statement:
--   The Height Descent Minors construction uses the map pi0 algebra Map padic Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L480-L480
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L480-L480

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.map_pi0_algebraMap_padicInt : PowerSeries.map (algebraMap ℤ_[l] O) (pi0 l ℤ_[l]) = pi0 l O := by sorry
