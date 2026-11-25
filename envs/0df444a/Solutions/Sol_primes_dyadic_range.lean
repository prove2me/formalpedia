-- Prove2me | solution 1 for primes_dyadic_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:04:13.140741+00:00
-- url     : https://prove2.me/submissions/75fe5943-6be8-410c-b3bf-e7edf1d45970

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PrimesDyadicRS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_ClaimOfTwo
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_RealIneq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallNaturalNumbersBound
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_PrimesDyadicRS
import Theorems.Thm_PI_PrimesDyadicRS_K_small_natural_numbers_bound
import Theorems.Thm_PI_PrimesDyadicRS_W_claim_of_two
import Theorems.Thm_PI_PrimesDyadicRS_W_real_dyadic_inequality


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.PrimesDyadicRS.Claim :=
  PI.PrimesDyadicRS.W.claim_of_two PI.PrimesDyadicRS.K.small_natural_numbers_bound PI.PrimesDyadicRS.W.real_dyadic_inequality
