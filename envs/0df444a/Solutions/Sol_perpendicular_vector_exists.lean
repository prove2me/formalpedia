-- Prove2me | solution 1 for perpendicular_vector_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:33:57.54062+00:00
-- url     : https://prove2.me/submissions/878a9d2b-b889-4a93-a8ee-90959416b71a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_PerpVecPerpSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_PerpendicularDeterminants_DetMemSubalgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_PerpendicularDeterminants_PerpVecOfPerp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_FormPartialDerivatives
import Theorems.Thm_PI_UnitaryGroupMassFormula_FormPartialDerivatives_perpVec_perp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : ReciprocityTheory.ChartRestriction.G.TB.PerpVecSt := by
  unfold ReciprocityTheory.ChartRestriction.G.TB.PerpVecSt
  intro R _ V _ _ p h e e' g c
  exact PI.UnitaryGroupMassFormula.FormPartialDerivatives.perpVec_perp R V p h e e' g c
