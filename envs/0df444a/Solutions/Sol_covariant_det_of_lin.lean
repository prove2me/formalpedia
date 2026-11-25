-- Prove2me | solution 1 for covariant_det_of_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:55:17.835509+00:00
-- url     : https://prove2.me/submissions/1f5f964f-588c-4a74-8b38-50f89ca62ca5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantDeterminantScaling_IntCastMulEqSmul
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnCovDet
import Theorems.Thm_PI_QnCovDetW_qnCovDet_of_lin


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.QnCovLin → PI.QnCovDet :=
  PI.QnCovDetW.qnCovDet_of_lin
