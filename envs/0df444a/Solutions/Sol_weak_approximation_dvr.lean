-- Prove2me | solution 1 for weak_approximation_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:18:54.031691+00:00
-- url     : https://prove2.me/submissions/31f3691f-7430-49dc-884d-23239d31f8e3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeakApproxDVR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_BigExistenceHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_RhoProjectionAssembly
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WeakApproxDVR
import Theorems.Thm_PI_WA_big_existence_holds
import Theorems.Thm_PI_WA_rho_projection_assembly
import Theorems.Thm_PI_WA_weakApproxDVR_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.WeakApproxDVR :=
  PI.WA.weakApproxDVR_of PI.WA.big_existence_holds PI.WA.rho_projection_assembly
