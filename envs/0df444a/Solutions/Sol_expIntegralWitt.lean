-- Prove2me | solution 1 for expIntegralWitt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:02:49.338137+00:00
-- url     : https://prove2.me/submissions/a11ae0b4-c8c0-4214-9d8d-ce6befb55ac3

import Definitions.Def_Formalism_PeriodIntegrals_ExpIntW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatMemWf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_StepIII
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_RootsOfUnityRingLeWittIntegers
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ExpIntW
import Theorems.Thm_PI_ExpIntWProof_expIntW_of_key
import Theorems.Thm_PI_ExpIntWProof_keyW
import Theorems.Thm_PI_ExpIntWProof_stepI


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.ExpIntW :=
  PI.ExpIntWProof.expIntW_of_key PI.ExpIntWProof.stepI PI.ExpIntWProof.keyW
