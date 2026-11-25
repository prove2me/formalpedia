-- Prove2me | solution 1 for minor_evaluation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:09:28.32681+00:00
-- url     : https://prove2.me/submissions/fab610a0-8563-4429-a7fc-70663cdffb1c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwEval
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionEvaluation_LsumEqOfSubset
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WwEval
import Theorems.Thm_PI_WwEvalWork_wwEval


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.WwEval.WwEval := PI.WwEvalWork.wwEval
