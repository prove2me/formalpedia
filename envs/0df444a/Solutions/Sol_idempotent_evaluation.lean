-- Prove2me | solution 1 for idempotent_evaluation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:02:49.61425+00:00
-- url     : https://prove2.me/submissions/fde3206b-78cb-4d48-89b8-d0b61110b7d8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_IdemDen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_IdempotentEvaluation_IdemEval
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_IdempotentEvaluation_DualDiff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_TBIdemDen
import Theorems.Thm_PI_UnitaryGroupMassFormula_TBIdemDen_idemEval


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : ReciprocityTheory.ChartRestriction.G.TB.IdemEvalSt := PI.UnitaryGroupMassFormula.TBIdemDen.idemEval
