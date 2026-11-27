-- Prove2me | solution 1 for isLattice_of_discriminant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:34:56.739284+00:00
-- url     : https://prove2.me/submissions/e4034955-6024-469f-bcd8-d2d6320bb261

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_UniformDiscreteness_FgOfUnifDiscrete
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_TBDisc
import Theorems.Thm_PI_UnitaryGroupMassFormula_TBDisc_isLatticeOfDisc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : ReciprocityTheory.ChartRestriction.G.TB.IsLatticeOfDiscSt :=
  PI.UnitaryGroupMassFormula.TBDisc.isLatticeOfDisc
