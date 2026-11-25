-- Prove2me | solution 1 for gelfand_tsetlin_scaling
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:17:20.484198+00:00
-- url     : https://prove2.me/submissions/e09b10ad-f470-4170-a7bc-21222580b121

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GTScale
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitPowerNormScale_NormUnitsZpowSq
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_GTScale
import Theorems.Thm_PI_GTS_gTScale


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.GTScale := PI.GTS.gTScale
