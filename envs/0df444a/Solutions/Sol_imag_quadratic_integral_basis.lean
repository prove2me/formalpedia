-- Prove2me | solution 1 for imag_quadratic_integral_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:01:00.839358+00:00
-- url     : https://prove2.me/submissions/99c8a93b-a4c7-4198-a357-4f352fcc362e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ClassNumImQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ClassNumberIntegrality_HalfIntegral
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ClassNumImQInt
import Theorems.Thm_PI_UnitaryGroupMassFormula_ClassNumImQInt_intBasis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.ClassNumImQ.IntBasis :=
  PI.UnitaryGroupMassFormula.ClassNumImQInt.intBasis
