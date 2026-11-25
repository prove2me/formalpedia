-- Prove2me | solution 1 for formal_group_add_generation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:03:55.666207+00:00
-- url     : https://prove2.me/submissions/61909771-d1f8-4869-a4e0-ca52d6fa7bec

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupPoints_AddGenThm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupPoints_MulGenThm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupPoints_ConstantCoeffLogEqZero
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FglPtW
import Theorems.Thm_PI_FglPtW_Wk_addGen_thm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.FglPtW.AddGen := PI.FglPtW.Wk.addGen_thm
