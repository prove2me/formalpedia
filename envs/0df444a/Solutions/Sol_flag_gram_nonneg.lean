-- Prove2me | solution 1 for flag_gram_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:05:59.578807+00:00
-- url     : https://prove2.me/submissions/4a410d24-c0a9-4784-83c9-8e0804b71447

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FlagGramNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_Gval
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FlagGramNonneg
import Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.FlagGramNonneg := PI.UnitaryGroupMassFormula.FlagGramNonneg.main
