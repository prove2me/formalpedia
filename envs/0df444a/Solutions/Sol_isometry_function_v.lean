-- Prove2me | solution 1 for isometry_function_v
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:12:41.773307+00:00
-- url     : https://prove2.me/submissions/ea472a11-ae2d-4154-b05c-46238f44b43f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoFunV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryFunctionSpace_InstFintypeOE
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IsoFunV
import Theorems.Thm_PI_IsoFunVW_isoFunV_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.IsoFunV.IsoFunV := PI.IsoFunVW.isoFunV_main
