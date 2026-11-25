-- Prove2me | solution 1 for weylForU_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:22:26.890105+00:00
-- url     : https://prove2.me/submissions/6e9dfc9f-0ec5-4f65-bbcc-891353c6c28f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeylForU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaUnitary_NatWCastReal
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WeylForU
import Theorems.Thm_PI_WeylForUWork_weylForU_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.ModelIso → PI.NablaDim → PI.WeylForU := PI.WeylForUWork.weylForU_of
