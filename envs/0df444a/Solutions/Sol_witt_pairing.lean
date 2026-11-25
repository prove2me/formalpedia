-- Prove2me | solution 1 for witt_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:18:06.280804+00:00
-- url     : https://prove2.me/submissions/5c3858b0-4269-42de-83dd-88b4b82567d5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittEndomorphism_WfEndOfLog
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittLogarithm
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittFrobeniusEnd
import Theorems.Thm_PI_WfEndProof_pairW


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.PairW := PI.WfEndProof.pairW
