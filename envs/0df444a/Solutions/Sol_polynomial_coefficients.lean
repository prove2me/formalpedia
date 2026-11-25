-- Prove2me | solution 1 for polynomial_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:07:36.556398+00:00
-- url     : https://prove2.me/submissions/7f7336c1-1ddf-4280-b800-939969a03841

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_IsPositiveDefiniteMatrixCoefficientOfMemAlgA
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_PolyCoef
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_polyCoef


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.PolyCoef := PI.UnitaryGroupMassFormula.PolyCoef.polyCoef
