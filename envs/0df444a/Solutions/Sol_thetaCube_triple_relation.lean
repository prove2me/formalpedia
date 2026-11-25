-- Prove2me | solution 1 for thetaCube_triple_relation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:08:22.346633+00:00
-- url     : https://prove2.me/submissions/cfc99a18-a762-4ff3-a5be-d84070f1c084

import Definitions.Def_Formalism_PeriodIntegrals_CubicExponentialFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubicExponentialFactor_ExpMvAddC
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CubicExponentialFactor
import Theorems.Thm_PI_CubicExponentialFactor_Wk_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.CubicExponentialFactor.Lemma := PI.CubicExponentialFactor.Wk.main
