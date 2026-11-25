-- Prove2me | solution 1 for discriminant_of_product_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:01:04.390862+00:00
-- url     : https://prove2.me/submissions/d6cde3a7-7b78-4f4c-9459-2d9086efd065

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_UniformDiscreteness_FgOfUnifDiscrete
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_TBDisc
import Theorems.Thm_PI_UnitaryGroupMassFormula_TBDisc_discOfProdLower


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : ReciprocityTheory.ChartRestriction.G.TB.DiscOfProdLowerSt :=
  PI.UnitaryGroupMassFormula.TBDisc.discOfProdLower
