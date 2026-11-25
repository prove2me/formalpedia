-- Prove2me | solution 1 for isPrime_span_of_jacobi_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:02:54.496871+00:00
-- url     : https://prove2.me/submissions/c055f2d4-82ba-4900-a84c-d75bd72e9653

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_InertPrime
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeJacobi_NotIsSquareOfJacobi
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_InertPrime
import Theorems.Thm_PI_InertPrimeWork_inert


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
theorem _root_.solution : PI.InertPrime := by
  intro K _ _ hK b d p hb hp hj
  exact PI.InertPrimeWork.inert K hK b d p hb hp hj
