-- Prove2me | solution 1 for local_dual_generation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:31:47.99325+00:00
-- url     : https://prove2.me/submissions/2bd59928-2ef1-4efc-a1fd-5b72850606f7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocDualGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_LocDualGenOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_UnramifiedDualGenerator
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_LocDualGen
import Theorems.Thm_PI_LocDualGen_FpU_unramified_dual_generator
import Theorems.Thm_PI_LocDualGen_Of_locDualGen_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.LocDualGen.Stmt :=
  PI.LocDualGen.Of.locDualGen_of PI.LocDualGen.FpU.unramified_dual_generator
