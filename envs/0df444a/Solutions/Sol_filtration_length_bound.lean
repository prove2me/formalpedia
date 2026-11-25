-- Prove2me | solution 1 for filtration_length_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:54:12.7768+00:00
-- url     : https://prove2.me/submissions/da996898-03b1-4248-ba33-1c56ee8f0b8a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FiltLen
import Definitions.Def_Formalism_PeriodIntegrals_FiltLenF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiltrationLength_FiltLenFMain
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FiltLenF
import Theorems.Thm_PI_FiltrationLength_filtLenF_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.FiltLenF := PI.FiltrationLength.filtLenF_main
