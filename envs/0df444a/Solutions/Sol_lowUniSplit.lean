-- Prove2me | solution 1 for lowUniSplit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:14:45.735938+00:00
-- url     : https://prove2.me/submissions/afa1edc3-b5d2-444c-a614-f55acb8adc7f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerUnipotentSplit_SecondFactorMemLowerTriangular
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_LowUniSplit
import Theorems.Thm_PI_LowUniSplit_lowSplit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : Formalism.FourierDecayAlt.C2.LowSplit := PI.LowUniSplit.lowSplit
