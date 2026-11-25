-- Prove2me | solution 1 for sum_log_p_over_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:37:11.288706+00:00
-- url     : https://prove2.me/submissions/02f8c142-592f-492d-bc9c-97242d8cd964

import Definitions.Def_Formalism_PeriodIntegrals_PrimeSums
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_PrimeLogOverPTop
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_PrimeLogOverP
import Theorems.Thm_PI_PrimeLogOverPWork_sum_log_div_prime_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.PrimeLogOverP := PI.PrimeLogOverPWork.sum_log_div_prime_le
