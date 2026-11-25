-- Prove2me | solution 1 for ramificationDegreeSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:10:52.45542+00:00
-- url     : https://prove2.me/submissions/7022c886-bb7e-4586-8f8d-6fdef801e749

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_EfRankSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RamificationRankSum_EfRankSumMain
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_EfRankSum
import Theorems.Thm_PI_UnitaryGroupMassFormula_EfRankSum_efRankSum_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.EfRankSum := PI.UnitaryGroupMassFormula.EfRankSum.efRankSum_main
