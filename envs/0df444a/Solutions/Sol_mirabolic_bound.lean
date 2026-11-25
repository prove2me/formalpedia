-- Prove2me | solution 1 for mirabolic_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:13:01.234096+00:00
-- url     : https://prove2.me/submissions/e7af40c0-b76b-4671-bbd2-89ecfa55065e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_MirabolicBound
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_GGMirBound
import Theorems.Thm_PI_GGMirBoundW_mirabolicBound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : Formalism.L2.SG.GGMirabolic.MirabolicBound :=
  PI.GGMirBoundW.mirabolicBound
