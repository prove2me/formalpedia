-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_minor_bound_extra_holds
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.minor_bound_extra_holds
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:37:27.405101+00:00
-- url     : https://prove2.me/theorems/1f8777bc-986e-4bec-be2e-dd678d6ade5e
-- title:
--   Height Descent Minors: minor bound extra holds
-- statement:
--   The Height Descent Minors construction uses the minor bound extra holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1566-L1650
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1566-L1650

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.minor_bound_extra_holds : MinorBoundExtra := by sorry
