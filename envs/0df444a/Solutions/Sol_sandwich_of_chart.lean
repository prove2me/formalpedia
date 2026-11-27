-- Prove2me | solution 1 for sandwich_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:34:17.113708+00:00
-- url     : https://prove2.me/submissions/396bfaa4-54be-42d9-86af-a81efbae3e7c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_SandwichOfOfCharts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_UnrealifyRL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_ChartZeroEqOneOfLongWeylSq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_SideAUnrealifyRL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_SideBUnrealifyRL
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_SwSandwichOf
import Theorems.Thm_PI_SwSandwichOfWork_chartBwd
import Theorems.Thm_PI_SwSandwichOfWork_chartFwd
import Theorems.Thm_PI_SwSandwichOfWork_logG
import Theorems.Thm_PI_SwSandwichOfWork_normRL
import Theorems.Thm_PI_SwSandwichOfWork_sandwichOf_of_charts
import Theorems.Thm_PI_SwSandwichOfWork_sideA
import Theorems.Thm_PI_SwSandwichOfWork_sideB


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.SwSand.SandwichOf :=
  PI.SwSandwichOfWork.sandwichOf_of_charts PI.SwSandwichOfWork.normRL PI.SwSandwichOfWork.logG
    PI.SwSandwichOfWork.chartFwd PI.SwSandwichOfWork.chartBwd PI.SwSandwichOfWork.sideB
    PI.SwSandwichOfWork.sideA
