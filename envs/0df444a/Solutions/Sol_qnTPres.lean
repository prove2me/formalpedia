-- Prove2me | solution 1 for qnTPres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:27:33.250036+00:00
-- url     : https://prove2.me/submissions/b2f26190-8135-4bad-9544-c3e79ed5803c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_SecondCapelliMinorContinuousLinear
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnTInv
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnTPres
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_qnTPres_of
import Theorems.Thm_qnTInv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : Formalism.FourierDecayAlt.Q.TPreservesFF := Formalism.FourierDecayAlt.Q.TPresMain.qnTPres_of qnTInv
