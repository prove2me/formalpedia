-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_action_laws_holds
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.action_laws_holds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:26:41.998439+00:00
-- url     : https://prove2.me/theorems/6c126c2e-82ec-44e4-965b-ad11b3ee1f5a
-- title:
--   Height Descent Minors: action laws holds
-- statement:
--   The Height Descent Minors construction uses the action laws holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L163-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L163-L181

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.action_laws_holds : ActLaws := by sorry
