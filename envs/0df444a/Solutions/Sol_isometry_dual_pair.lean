-- Prove2me | solution 1 for isometry_dual_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:12:39.76899+00:00
-- url     : https://prove2.me/submissions/8c45add5-ec04-45cb-bc07-0ce1ca9bb866

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDualPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDualPair_SymmetricMeasureL2NormEqResolutionL2
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IsoDualPair
import Theorems.Thm_PI_IsoDualPair_UnitaryGroupMassFormula_isoDualPair


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.IsoDualPair.IsoDualPair := PI.IsoDualPair.UnitaryGroupMassFormula.isoDualPair
