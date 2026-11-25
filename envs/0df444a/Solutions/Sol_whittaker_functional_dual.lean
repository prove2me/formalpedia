-- Prove2me | solution 1 for whittaker_functional_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:17:24.289495+00:00
-- url     : https://prove2.me/submissions/698b2fef-9d47-4e62-a5f7-324439a82413

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WhitFunctDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WhittakerFunctionalDual_StableOfIrreducible
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WhitFunctDual
import Theorems.Thm_PI_WhitFunctDualWork_whitFunctDual_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.WhitFunctDual := PI.WhitFunctDualWork.whitFunctDual_main
