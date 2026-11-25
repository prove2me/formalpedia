-- Prove2me | solution 1 for sc_pi_construction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:22:20.697002+00:00
-- url     : https://prove2.me/submissions/65ad2d34-35bb-4067-a9a9-4441c9aa1406

import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_InnerOfNorm
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ScPiBuild
import Theorems.Thm_PI_ScPiBuildW_Asm_build


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.ScPiExists.Build :=
  PI.ScPiBuildW.Asm.build
