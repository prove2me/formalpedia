-- Prove2me | solution 1 for standard_slope_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:05:02.179203+00:00
-- url     : https://prove2.me/submissions/4e0e7951-d6d2-4979-884c-722d33bee0d1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_HookBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_NablaGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_NablaOperatorBasis
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_StdSlopeLow
import Theorems.Thm_PI_SlopeSteps_gram_matrix_duality
import Theorems.Thm_PI_SlopeSteps_nabla_gram_lower_bound
import Theorems.Thm_PI_SlopeSteps_nabla_operator_basis
import Theorems.Thm_PI_SlopeSteps_stdSlopeLow_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.StdSlopeLow :=
  PI.SlopeSteps.stdSlopeLow_of PI.SlopeSteps.nabla_gram_lower_bound PI.SlopeSteps.gram_matrix_duality
    PI.SlopeSteps.nabla_operator_basis
