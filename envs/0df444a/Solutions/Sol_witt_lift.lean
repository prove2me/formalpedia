-- Prove2me | solution 1 for witt_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:17:29.923746+00:00
-- url     : https://prove2.me/submissions/33fe2c18-9a10-4816-91b1-e42d74732a45

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ArtSch
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittCoefficients_CoeffEqOfSubMem
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ASWitt
import Theorems.Thm_PI_ArtSch_WittLiftWork_wittLift


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.ArtSch.WittLift := PI.ArtSch.WittLiftWork.wittLift
