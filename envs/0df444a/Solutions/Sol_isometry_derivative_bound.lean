-- Prove2me | solution 1 for isometry_derivative_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:17:31.72792+00:00
-- url     : https://prove2.me/submissions/afa99ce4-61fa-4baa-b026-70bfd8e4e1de

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDerivB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_IsoDerivB
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IsoDerivB
import Theorems.Thm_PI_IsoDerivBFintype_isoDerivB


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.IsoDerivB.IsoDerivB := PI.IsoDerivBFintype.isoDerivB
