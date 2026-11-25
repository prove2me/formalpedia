-- Prove2me | solution 1 for positive_definite_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:16:44.206841+00:00
-- url     : https://prove2.me/submissions/a88aa462-da18-45bb-a331-9d5d2103fa18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FinOrdAd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PositiveDefiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PositiveDefiniteness_SplittingOfExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PositiveDefiniteness_PositiveDefiniteSecond
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_DefPosDef
import Theorems.Thm_PI_DefPosDefWork_defPosDef_of
import Theorems.Thm_PI_DefPosDefWork_positive_definite_second
import Theorems.Thm_PI_DefPosDefWork_splitting_of_extension


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.DefPosDef :=
  PI.DefPosDefWork.defPosDef_of PI.DefPosDefWork.splitting_of_extension PI.DefPosDefWork.positive_definite_second
