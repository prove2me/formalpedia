-- Prove2me | solution 1 for productFramesDense_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:04:16.317042+00:00
-- url     : https://prove2.me/submissions/8d6a08c4-0170-4c82-a156-d7e23ac26449

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_VanishInvertible
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_Decomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_Derived
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnitaryDense
import Theorems.Thm_PI_UD_framesDense_of
import Theorems.Thm_PI_UD_gramStep
import Theorems.Thm_PI_UD_svdStep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.FramesDense := PI.UD.framesDense_of PI.UD.svdStep PI.UD.gramStep
