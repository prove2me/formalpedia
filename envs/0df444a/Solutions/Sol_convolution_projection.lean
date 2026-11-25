-- Prove2me | solution 1 for convolution_projection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:04:05.366459+00:00
-- url     : https://prove2.me/submissions/6729a7c5-8423-45ac-8e15-d3c0eed8c97c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhConvProj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConvolutionProjection_ConvProjOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConvolutionProjection_SelfAdj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConvolutionProjection_UrepMulApply
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_PhConvProj
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhConvProj_Defs_convProj_of
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhConvProj_Sand_sand
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhConvProj_SelfAdj_selfAdj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.PhConvProj.ConvProj :=
  PI.UnitaryGroupMassFormula.PhConvProj.Defs.convProj_of PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj.selfAdj PI.UnitaryGroupMassFormula.PhConvProj.Sand.sand
