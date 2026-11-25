-- Prove2me | solution 1 for posDefCongruentOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:15:29.924861+00:00
-- url     : https://prove2.me/submissions/e9807427-d2e1-496b-af78-d0bf613c4f98

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_AdelicCompactOpens_HermDefONFamily
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianDefiniteOrthonormal_Imports
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_HermDefON
import Theorems.Thm_PI_UnitaryGroupMassFormula_HermDefON_exists_congr_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : Formalism.L2.Props.HermDefON := fun _ G hG => PI.UnitaryGroupMassFormula.HermDefON.exists_congr_one G hG
