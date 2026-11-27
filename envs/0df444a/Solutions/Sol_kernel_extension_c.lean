-- Prove2me | solution 1 for kernel_extension_c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:35:01.689394+00:00
-- url     : https://prove2.me/submissions/01649971-cb01-493d-b1bd-ef6ea8054d29

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConstantCoefficientKernel_RingHomCoeffZero
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_KerExtC
import Theorems.Thm_PI_KerExtCWork_extC


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.KerIso.ExtC := PI.KerExtCWork.extC
