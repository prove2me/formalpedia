-- Prove2me | solution 1 for perpendicular_vector_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:34:06.874493+00:00
-- url     : https://prove2.me/submissions/c7322b93-b289-4917-99e8-ffe4696be9e8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_PerpVecPerpSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_PerpendicularDeterminants_DetMemSubalgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_PerpendicularDeterminants_PerpVecOfPerp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_FormPartialDerivatives
import Theorems.Thm_PI_UnitaryGroupMassFormula_FormPartialDerivatives_perpVec_of_perp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : ReciprocityTheory.ChartRestriction.G.TB.PerpVecPerpSt := by
  unfold ReciprocityTheory.ChartRestriction.G.TB.PerpVecPerpSt
  intro R _ V _ _ p h e e' g hg
  exact PI.UnitaryGroupMassFormula.FormPartialDerivatives.perpVec_of_perp R V p h e e' g hg
