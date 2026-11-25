-- Prove2me | solution 1 for scGapBig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:18:50.878355+00:00
-- url     : https://prove2.me/submissions/ffb3fc9a-07cf-41c0-b6e5-0343c56e84c1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScGapBig
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SpectralGapLarge_ScGapBigMain
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ScGapBig
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScGapBig_scGapBig_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.ScGapBig.ScGapBig := PI.UnitaryGroupMassFormula.ScGapBig.scGapBig_main
