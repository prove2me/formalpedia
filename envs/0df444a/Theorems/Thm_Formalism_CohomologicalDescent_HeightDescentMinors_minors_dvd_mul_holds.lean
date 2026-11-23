-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_minors_dvd_mul_holds
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.minors_dvd_mul_holds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:11.522542+00:00
-- url     : https://prove2.me/theorems/488aa824-c2ca-46ee-90fe-681cb283bab3
-- title:
--   Height Descent Minors: minors dvd mul holds
-- statement:
--   The Height Descent Minors construction uses the minors dvd mul holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1549-L1551
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1549-L1551

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.minors_dvd_mul_holds : MinorsDvdMul := by sorry
