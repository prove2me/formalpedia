-- Prove2me | solution 1 for scalar_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:20:26.650499+00:00
-- url     : https://prove2.me/submissions/cea8f5b3-d755-40d4-bdca-45fc8cbed021

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScalDeg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarDegree_ScalDegMain
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ScalDeg
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScalDeg_scalDeg_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.ScalDeg.ScalDeg := PI.UnitaryGroupMassFormula.ScalDeg.scalDeg_main
