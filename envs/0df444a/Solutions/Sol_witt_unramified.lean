-- Prove2me | solution 1 for witt_unramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:18:10.241051+00:00
-- url     : https://prove2.me/submissions/71537adc-6a2b-4151-8c8e-e45ba435f8e1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WittUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittUnramified_WittUnramMain
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittUnram
import Theorems.Thm_PI_WittUnramWork_wittUnram_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.WittUnram :=
  PI.WittUnramWork.wittUnram_main
