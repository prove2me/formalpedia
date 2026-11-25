-- Prove2me | solution 1 for unit_kronecker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:04:15.877232+00:00
-- url     : https://prove2.me/submissions/073b4103-2ccd-44a1-a819-139e9133112d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitKron
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_PosDefFormNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_EqZeroOfMulVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_IntRootProp
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnitKron
import Theorems.Thm_PI_UnitKronW_stepA
import Theorems.Thm_PI_UnitKronW_stepB
import Theorems.Thm_PI_UnitKronW_stepC
import Theorems.Thm_PI_UnitKronW_unitKron_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.UnitKron :=
  PI.UnitKronW.unitKron_of PI.UnitKronW.stepA PI.UnitKronW.stepB PI.UnitKronW.stepC
