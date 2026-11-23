-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_pi0_padicInt_algebraMap
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.map_pi0_padicInt_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:59.966489+00:00
-- url     : https://prove2.me/theorems/76f5a00d-6492-40e2-a4fe-2f787fea56d9
-- title:
--   Height Descent Minors: map pi0 padic Int algebra Map
-- statement:
--   The Height Descent Minors construction uses the map pi0 padic Int algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1200-L1200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1200-L1200

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.map_pi0_padicInt_algebraMap : PowerSeries.map (algebraMap ℤ_[l] O) (pi0 l ℤ_[l]) = pi0 l O := by sorry
