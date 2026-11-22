-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_fourth_relation_holds
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.fourth_relation_holds
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:28:55.303412+00:00
-- url     : https://prove2.me/theorems/4a39bd3f-3f90-43a7-b272-0281f2c3e890
-- title:
--   Height Descent Minors: fourth relation holds
-- statement:
--   The Height Descent Minors construction uses the fourth relation holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1938-L1938
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1938-L1938

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.fourth_relation_holds : R4 := by sorry
