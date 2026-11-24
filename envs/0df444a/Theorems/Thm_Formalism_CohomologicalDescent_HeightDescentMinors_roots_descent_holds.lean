-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_roots_descent_holds
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.roots_descent_holds
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:37:23.830701+00:00
-- url     : https://prove2.me/theorems/2b6c0130-5bb8-47ee-987b-8a624823f22b
-- title:
--   Height Descent Minors: roots descent holds
-- statement:
--   The Height Descent Minors construction uses the roots descent holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1942-L1942
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1942-L1942

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.roots_descent_holds : RootsDescent := by sorry
