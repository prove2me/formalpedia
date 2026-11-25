-- Prove2me | solution 1 for formal_group_mul_generation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:01:00.596143+00:00
-- url     : https://prove2.me/submissions/555c68bb-4e05-453e-855f-339caea283bf

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupPoints_AddGenThm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupPoints_MulGenThm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupPoints_ConstantCoeffLogEqZero
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FglPtW
import Theorems.Thm_PI_FglPtW_Wk_mulGen_thm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.FglPtW.MulGen := PI.FglPtW.Wk.mulGen_thm
