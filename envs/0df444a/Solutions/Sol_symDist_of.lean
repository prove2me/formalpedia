-- Prove2me | solution 1 for symDist_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:10:28.765728+00:00
-- url     : https://prove2.me/submissions/aa8083b0-cd26-43bc-b0fe-b09f555e748f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SymDist
import Definitions.Def_Formalism_PeriodIntegrals_ExpTri
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SymmetricDistance_SymDistOf
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_SymDist
import Theorems.Thm_PI_SymDistWork_symDist_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.ExpTri → PI.SymDist := PI.SymDistWork.symDist_of
