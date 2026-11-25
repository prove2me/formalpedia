-- Prove2me | solution 1 for covariant_hat_sq_of_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:39:33.425422+00:00
-- url     : https://prove2.me/submissions/350cd387-7b97-4159-a029-d7732ebadebf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ContractionsCovariantIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_QnCovHat2OfLin
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CovariantHatSqOfLin
import Theorems.Thm_PI_QnCovHat2W_qnCovHat2_of_lin


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.QnCovLin → PI.QnCovHat2 := PI.QnCovHat2W.qnCovHat2_of_lin
