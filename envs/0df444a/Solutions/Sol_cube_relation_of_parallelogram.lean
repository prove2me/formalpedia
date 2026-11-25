-- Prove2me | solution 1 for cube_relation_of_parallelogram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:13:59.894548+00:00
-- url     : https://prove2.me/submissions/4ac3bf92-1a72-443a-aa47-17ebd8447e2c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_IsExpIntegralParallelogramOfNe
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CubeRelationOfParallelogram
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_cubeRelationOfParallelogram


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.FglGram.CubeRelationOfParallelogram := PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.cubeRelationOfParallelogram
