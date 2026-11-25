-- Prove2me | solution 1 for finiteAdeleIntegers_compactOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:02:54.228993+00:00
-- url     : https://prove2.me/submissions/b735fe93-55b4-43b0-99a7-207c97902bb1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_AdelicCompactOpens_IntAdelesCompactOpen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicIntegersCompact_IsCompactAdicCompletionIntegers
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IntAdCpctOpen
import Theorems.Thm_PI_IntAdCpctOpenWork_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : Formalism.L2.Props.IntAdelesCompactOpen := PI.IntAdCpctOpenWork.main
