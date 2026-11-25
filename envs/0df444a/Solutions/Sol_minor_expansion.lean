-- Prove2me | solution 1 for minor_expansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:09:29.991442+00:00
-- url     : https://prove2.me/submissions/62ab71d7-4893-4f76-90e6-872638305b6d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwMinorExpand
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorExpansion_WwMinorExpandMain
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WwMinorExpand
import Theorems.Thm_PI_WwMinorExpandWork_wwMinorExpand_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.WwMinorExpand.WwMinorExpand := PI.WwMinorExpandWork.wwMinorExpand_main
