-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_q_padic
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.map_q_padic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:08.245895+00:00
-- url     : https://prove2.me/theorems/b8408fd3-ee2f-4f6c-b2da-91876372f763
-- title:
--   Height Descent Minors: map q padic
-- statement:
--   The Height Descent Minors construction uses the map q padic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L482-L482
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L482-L482

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.map_q_padic : PowerSeries.map (algebraMap ℤ_[l] O) (q l ℤ_[l]) = q l O := by sorry
