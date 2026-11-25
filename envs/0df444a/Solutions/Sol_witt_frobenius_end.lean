-- Prove2me | solution 1 for witt_frobenius_end
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:31:37.482341+00:00
-- url     : https://prove2.me/submissions/2717bf6e-e051-49e9-bcde-a45dfddf09bd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittEndomorphism_WfEndOfLog
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittLogarithm
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittFrobeniusEnd
import Theorems.Thm_PI_WfEndProof_wfEnd_of_log
import Theorems.Thm_witt_logarithm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.WfEnd := PI.WfEndProof.wfEnd_of_log witt_logarithm
