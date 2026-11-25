-- Prove2me | solution 1 for stabilizer_large
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:22:22.685247+00:00
-- url     : https://prove2.me/submissions/23daef55-e265-4324-b121-39edad450b51

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_StabBig
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LargeStabilizerInverse_GLeftInv
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_StabBig
import Theorems.Thm_PI_StabBigW_stabBig


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.StabBig := PI.StabBigW.stabBig
