-- Prove2me | solution 1 for kernel_self_dual_of_different
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:12:57.945072+00:00
-- url     : https://prove2.me/submissions/105720d4-e063-4bf4-8f04-cbdbf2949ce5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualOfDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualDifferent_SelfDualOfDiff
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_KerSelfDual
import Theorems.Thm_PI_UnitaryGroupMassFormula_KerSelfDual_selfDualOfDiff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.KerIso.SelfDualOfDiff := PI.UnitaryGroupMassFormula.KerSelfDual.selfDualOfDiff
