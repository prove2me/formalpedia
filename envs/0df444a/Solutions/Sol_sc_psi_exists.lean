-- Prove2me | solution 1 for sc_psi_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:20:22.154611+00:00
-- url     : https://prove2.me/submissions/85856cf4-74bd-4036-9a82-c9baae2a5443

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPsiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingTraceSumAlt_NormUnitsOfCalculation
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ScPsiExists
import Theorems.Thm_PI_ScPsiExists_UnitaryGroupMassFormula_norm_units_of_calculation


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.ScPsiExists.Target :=
  PI.ScPsiExists.UnitaryGroupMassFormula.norm_units_of_calculation
