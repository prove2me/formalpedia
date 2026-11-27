-- Prove2me | solution 1 for entireStatements_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:34:40.259652+00:00
-- url     : https://prove2.me/submissions/9a7525df-d64d-4b63-9351-ea84c98e50a2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VacEntire
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_VacuumEntire_AnalyticAtHfLeft
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_VacEntire
import Theorems.Thm_PI_VacEntire_UnitaryGroupMassFormula_iopEntire
import Theorems.Thm_PI_VacEntire_UnitaryGroupMassFormula_tensEntire


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.VacEntire.Target :=
  ⟨PI.VacEntire.UnitaryGroupMassFormula.iopEntire, PI.VacEntire.UnitaryGroupMassFormula.tensEntire⟩
