-- Prove2me | solution 1 for wfEnd_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:34:30.137013+00:00
-- url     : https://prove2.me/submissions/225ab273-4465-4c2f-9c4b-3f629f84834a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittEndomorphism_WfEndOfLog
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittLogarithm
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittFrobeniusEnd
import Theorems.Thm_PI_WfEndProof_wfEnd_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.WfRing → PI.WfSubst → PI.WfLog → PI.WfEnd := PI.WfEndProof.wfEnd_of
