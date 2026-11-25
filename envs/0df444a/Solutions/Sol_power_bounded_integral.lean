-- Prove2me | solution 1 for power_bounded_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:16:45.664466+00:00
-- url     : https://prove2.me/submissions/a460cd42-542d-49fa-bb36-5758fee47cca

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PowBddInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerBoundedIntegrality_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerBoundedIntegrality_EvalIntMapEqZero
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_PowBddInt
import Theorems.Thm_PI_PowBddIntWork_powBddInt_of
import Theorems.Thm_PI_PowBddIntWork_stepA
import Theorems.Thm_PI_PowBddIntWork_stepB


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.PowBddInt :=
  PI.PowBddIntWork.powBddInt_of PI.PowBddIntWork.stepA PI.PowBddIntWork.stepB
