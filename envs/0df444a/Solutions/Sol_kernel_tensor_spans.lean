-- Prove2me | solution 1 for kernel_tensor_spans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:09:24.8348+00:00
-- url     : https://prove2.me/submissions/3c858a92-fe3f-4557-869c-235615681c0b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerTens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorSpanning_TensSpans
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_KerTens
import Theorems.Thm_PI_KerTens_W_tensSpans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.KerTens.TensSpans := PI.KerTens.W.tensSpans
