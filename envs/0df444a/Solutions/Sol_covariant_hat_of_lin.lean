-- Prove2me | solution 1 for covariant_hat_of_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:03:34.911813+00:00
-- url     : https://prove2.me/submissions/2562408e-c80d-490c-9046-742f634c2c15

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatDecomposition_SkipOneEqSuccAbove
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnCovHat
import Theorems.Thm_PI_QnCovHatW_qnCovHat_of_lin


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.QnCovLin → PI.QnCovHat :=
  PI.QnCovHatW.qnCovHat_of_lin
