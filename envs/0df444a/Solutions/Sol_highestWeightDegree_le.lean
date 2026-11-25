-- Prove2me | solution 1 for highestWeightDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:17:29.838853+00:00
-- url     : https://prove2.me/submissions/5bf5ea28-6704-44fc-90cc-d28226d1cc4d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockWeightDegree_ExistsMonomialWeight
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FockWtDeg
import Theorems.Thm_PI_FockWtDegWork_wtDeg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.FockDegreeTwoParts.WtDeg := PI.FockWtDegWork.wtDeg
