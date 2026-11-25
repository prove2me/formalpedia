-- Prove2me | solution 1 for unipVal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:04:12.960929+00:00
-- url     : https://prove2.me/submissions/2e4b1441-18ee-48fc-bd8c-c9f3c0730ac1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnipVal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentValuation_VwIntEqZero
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnipVal
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnipVal_Main_part1
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnipVal_Main_part2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.UnipVal.UnipVal := fun _ _ _ w =>
  ⟨fun n hn => PI.UnitaryGroupMassFormula.UnipVal.Main.part1 w n hn,
    fun g₁ g₂ a h1 h2 h12 => PI.UnitaryGroupMassFormula.UnipVal.Main.part2 w g₁ g₂ a h1 h2 h12⟩
