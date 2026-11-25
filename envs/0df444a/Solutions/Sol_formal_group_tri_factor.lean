-- Prove2me | solution 1 for formal_group_tri_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:01:04.51559+00:00
-- url     : https://prove2.me/submissions/e4230ffa-5a20-4e93-ab22-70a04e44b807

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglTriFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_CcPrEq
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FglTriFactor
import Theorems.Thm_PI_FglTriFactor_Wk_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.FglTriFactor.Lemma := PI.FglTriFactor.Wk.main
