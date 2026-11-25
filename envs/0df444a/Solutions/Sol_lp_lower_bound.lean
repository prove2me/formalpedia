-- Prove2me | solution 1 for lp_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:09:26.327934+00:00
-- url     : https://prove2.me/submissions/43076780-947f-4724-bc14-3ffd61667128

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LpLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LinearProgramLowerBound_LpFeasibleLe
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_LpLower
import Theorems.Thm_PI_lpLower_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.LpLower := PI.lpLower_main
