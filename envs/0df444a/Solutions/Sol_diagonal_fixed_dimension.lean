-- Prove2me | solution 1 for diagonal_fixed_dimension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:28:14.488056+00:00
-- url     : https://prove2.me/submissions/c4a90d0d-4c70-4a8f-9fee-761fa2d9f071

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ClassAct
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FixedDimensionCount_ExistsSemidirectDecomposition
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_DiaFixDim
import Theorems.Thm_PI_UnitaryGroupMassFormula_DiaFixDim_Main_fixedDim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : Formalism.L2.SG.ClassAct.FixedDim := PI.UnitaryGroupMassFormula.DiaFixDim.Main.fixedDim
