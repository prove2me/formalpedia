-- Prove2me | solution 1 for low_smooth_of_k_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:07:47.555164+00:00
-- url     : https://prove2.me/submissions/40ae877b-38ec-46d1-b8c2-e1f71577a7e6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LowCyc
import Definitions.Def_Formalism_PeriodIntegrals_KFinSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_LowSmooth
import Theorems.Thm_PI_UnitaryGroupMassFormula_LowSmooth_lowSmooth_of_kFinSmooth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.KFinSmooth → PI.LowSmooth := PI.UnitaryGroupMassFormula.LowSmooth.lowSmooth_of_kFinSmooth
