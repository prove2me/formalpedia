-- Prove2me | solution 1 for perpendicular_vector_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:34:02.281265+00:00
-- url     : https://prove2.me/submissions/1b2835b2-5eac-47f6-9af3-7b47d1f29b93

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_PerpVecPerpSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_PerpendicularDeterminants_DetMemSubalgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_PerpendicularDeterminants_PerpVecOfPerp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_FormPartialDerivatives
import Theorems.Thm_PI_UnitaryGroupMassFormula_FormPartialDerivatives_perpVec_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : ReciprocityTheory.ChartRestriction.G.TB.PerpVecIntSt := by
  unfold ReciprocityTheory.ChartRestriction.G.TB.PerpVecIntSt
  intro R _ O V _ _ p h L hL e e' g he he' hg
  exact PI.UnitaryGroupMassFormula.FormPartialDerivatives.perpVec_int R O V p h L hL e e' g he he' hg
