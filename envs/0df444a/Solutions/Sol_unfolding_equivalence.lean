-- Prove2me | solution 1 for unfolding_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:10:36.869722+00:00
-- url     : https://prove2.me/submissions/27809bf6-c7f6-4271-a464-2b07ff6330ab

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_CompSymmComp
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnfoldEquiv
import Theorems.Thm_PI_UnfoldEquiv_UnitaryGroupMassFormula_unfoldEquiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.UnfoldEquiv.UnfoldEquiv := PI.UnfoldEquiv.UnitaryGroupMassFormula.unfoldEquiv
