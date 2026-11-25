-- Prove2me | solution 1 for dual_difference
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:26:32.381539+00:00
-- url     : https://prove2.me/submissions/f5cbada4-3804-494e-816f-20349e26c2b4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_IdemDen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_IdempotentEvaluation_IdemEval
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_IdempotentEvaluation_DualDiff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_TBIdemDen
import Theorems.Thm_PI_UnitaryGroupMassFormula_TBIdemDen_dualDiff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : ReciprocityTheory.ChartRestriction.G.TB.DualDiffSt := PI.UnitaryGroupMassFormula.TBIdemDen.dualDiff
