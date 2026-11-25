-- Prove2me | solution 1 for harmonicSplitting_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:28:44.626333+00:00
-- url     : https://prove2.me/submissions/88e65cc1-1654-4a75-a4f2-b42d2e78e4b2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_MinusPartOfMem
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FockHarmSplit
import Theorems.Thm_PI_FHS_harmSplit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.FockDegreeTwoParts.HarmSplit := PI.FHS.harmSplit
