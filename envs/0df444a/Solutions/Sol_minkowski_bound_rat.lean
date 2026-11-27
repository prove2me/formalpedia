-- Prove2me | solution 1 for minkowski_bound_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:35:43.33955+00:00
-- url     : https://prove2.me/submissions/72ef803e-1877-48e3-958f-f9bcd5eac4f6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_MinkowskiQ
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_Minkowski
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiTorsionFree_Lattice
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_MinkowskiQ
import Theorems.Thm_PI_MkQ_minkowskiBoundQ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.MinkowskiBoundQ := PI.MkQ.minkowskiBoundQ
