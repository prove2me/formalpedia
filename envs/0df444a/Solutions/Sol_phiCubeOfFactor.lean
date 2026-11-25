-- Prove2me | solution 1 for phiCubeOfFactor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:11:56.500343+00:00
-- url     : https://prove2.me/submissions/aaa1791f-4ca6-43b2-a9af-8567c52eb34e

import Definitions.Def_Formalism_PeriodIntegrals_PhiCubeOfFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialFactorIdentity_ExpMvEq
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_PhiCubeOfFactor
import Theorems.Thm_PI_PhiCubeOfFactor_Wk_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.PhiCubeOfFactor.Lemma := PI.PhiCubeOfFactor.Wk.main
