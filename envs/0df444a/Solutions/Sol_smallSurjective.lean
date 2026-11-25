-- Prove2me | solution 1 for smallSurjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:11:52.367826+00:00
-- url     : https://prove2.me/submissions/cf40c712-7c63-4b96-963a-0bc34d820edc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ArtSch
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmallArtinSchreier_ExistsAsOfValLtOne
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ASSmall
import Theorems.Thm_PI_UnitaryGroupMassFormula_ASSmall_tiltSmall


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.ArtSch.TiltSmall := PI.UnitaryGroupMassFormula.ASSmall.tiltSmall
