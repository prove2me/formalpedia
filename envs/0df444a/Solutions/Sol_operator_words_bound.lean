-- Prove2me | solution 1 for operator_words_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:17:33.504676+00:00
-- url     : https://prove2.me/submissions/de68ebd7-e507-492e-909f-378e29456de1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DualFockLinear_OpBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_Assemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_VanishMain
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_OpWords
import Theorems.Thm_PI_OpWords_opBound_of_vanish
import Theorems.Thm_PI_OpWords_vanishingOnQuadric


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : Formalism.MainNotions.TestSideCounting.OpBound :=
  PI.OpWords.opBound_of_vanish PI.OpWords.vanishingOnQuadric
