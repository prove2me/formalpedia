-- Prove2me | solution 1 for kernel_split_of_jacobi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:56:59.505008+00:00
-- url     : https://prove2.me/submissions/e31f1340-d3ac-4193-af01-01f5506d693d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualOfDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KernelSplitting_IsIntegralHalf
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_KerSplit
import Theorems.Thm_PI_UnitaryGroupMassFormula_KerSplit_splitsAt_odd
import Theorems.Thm_PI_UnitaryGroupMassFormula_KerSplit_splitsAt_two


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.KerIso.SplitOfJacobi := by
  intro K E _ _ _ _ _ cj d p s hd hs hcj hp hJ
  by_cases h2 : p = 2
  · subst h2
    exact PI.UnitaryGroupMassFormula.KerSplit.splitsAt_two cj d s hd hs hcj
  · exact PI.UnitaryGroupMassFormula.KerSplit.splitsAt_odd cj d p s hs hcj hp h2 (hJ.resolve_left h2)
