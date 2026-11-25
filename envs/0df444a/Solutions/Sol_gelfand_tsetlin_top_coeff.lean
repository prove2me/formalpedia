-- Prove2me | solution 1 for gelfand_tsetlin_top_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:17:24.3255+00:00
-- url     : https://prove2.me/submissions/8e5f7ab9-0742-4831-bf0e-ad1ca4dc8f32

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GTCoefTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_GTCoefTopMain
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_GTCoefTop
import Theorems.Thm_PI_GTNum_gTCoefTop_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.GTCoefTop := PI.GTNum.gTCoefTop_main
