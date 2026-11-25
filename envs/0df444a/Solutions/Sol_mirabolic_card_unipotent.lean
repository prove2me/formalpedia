-- Prove2me | solution 1 for mirabolic_card_unipotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:13:05.216389+00:00
-- url     : https://prove2.me/submissions/27b4cd02-9db3-4863-9cf6-207c1c5dcdf6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCardinality_UniMatUpper
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_GGCardUni
import Theorems.Thm_PI_GGCardUniWork_cardUni


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : Formalism.L2.SG.GGMirabolic.CardUni := PI.GGCardUniWork.cardUni
