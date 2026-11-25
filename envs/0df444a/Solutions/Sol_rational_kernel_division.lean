-- Prove2me | solution 1 for rational_kernel_division
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:09:28.338314+00:00
-- url     : https://prove2.me/submissions/d2af779e-989b-44f3-91a9-2d8fe54f9914

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalKernels_AsAlgApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalKernels_OfMulEps
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_DvRatKer
import Theorems.Thm_PI_Dv_RK_eG_mem
import Theorems.Thm_PI_Dv_RK_form_eq
import Theorems.Thm_PI_Dv_RK_rat_ker
import Theorems.Thm_PI_Dv_RK_tau_eps_ne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.Dv.Conclusion8 := by
  intro K _ σ G _ _ T P0 hM1 EE _ _ ρE M hR
  have hF := PI.Dv.RK.eG_mem T P0 (PI.Dv.RK.tau_eps_ne T P0 hM1)
  exact ⟨PI.Dv.RK.rat_ker M P0 hF hR, PI.Dv.RK.form_eq M P0 hF⟩
