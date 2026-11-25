-- Prove2me | solution 1 for transference_covering_divisor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:18:23.532795+00:00
-- url     : https://prove2.me/submissions/804dc2d0-06e1-4bf1-92ff-e031402e7948

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_TransferenceCoverRad
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CoveringRadius_CoverRad
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TransferenceCoveringDivisor
import Theorems.Thm_PI_Tr2_coverDiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.TransferenceCoverDiv := PI.Tr2.coverDiv
