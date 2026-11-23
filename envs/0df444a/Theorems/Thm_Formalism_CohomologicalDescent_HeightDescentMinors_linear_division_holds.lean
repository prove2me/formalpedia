-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_linear_division_holds
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.linear_division_holds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:29:02.829644+00:00
-- url     : https://prove2.me/theorems/5bbf9460-ae0d-4bf7-b12a-efa46c205b02
-- title:
--   Height Descent Minors: linear division holds
-- statement:
--   The Height Descent Minors construction uses the linear division holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1686-L1708
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1686-L1708

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.linear_division_holds : LinDivision := by sorry
