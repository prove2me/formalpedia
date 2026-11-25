-- Prove2me | solution 1 for prime_log_over_sq_tail
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:25:53.383015+00:00
-- url     : https://prove2.me/submissions/f1f87c8a-260c-43f4-b235-fcf700ff6f4d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PrimeSums
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PrimeLogarithmTail_SumLogDivSqLeDiv
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_PrimeLogOverPSqTail
import Theorems.Thm_PI_TailWork_sum_log_div_sq_le_div


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.PrimeLogOverPSqTail :=
  fun X hX Q hQ => PI.TailWork.sum_log_div_sq_le_div X hX Q hQ
