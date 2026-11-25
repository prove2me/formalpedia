-- Prove2me | solution 1 for gramExpansion_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:08:08.144127+00:00
-- url     : https://prove2.me/submissions/94d845b5-b542-4456-974f-ee585889f4f3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramUnitMultiplication_BeMulByZero
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_GramUnit
import Theorems.Thm_PI_UnitaryGroupMassFormula_GramUnit_gramUnit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.FglGram.GramUnit := PI.UnitaryGroupMassFormula.GramUnit.gramUnit
