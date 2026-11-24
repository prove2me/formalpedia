-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_minors_divide_all_holds
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.minors_divide_all_holds
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:37:26.773139+00:00
-- url     : https://prove2.me/theorems/207bd741-94a3-44ce-bdc1-c7a86ce30d92
-- title:
--   Height Descent Minors: minors divide all holds
-- statement:
--   The Height Descent Minors construction uses the minors divide all holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1545-L1547
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1545-L1547

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.minors_divide_all_holds : MinorsDvdAll := by sorry
