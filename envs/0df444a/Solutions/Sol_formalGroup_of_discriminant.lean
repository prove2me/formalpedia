-- Prove2me | solution 1 for formalGroup_of_discriminant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:06:02.52628+00:00
-- url     : https://prove2.me/submissions/c0ea67f4-d899-4740-9a15-4fa3701983eb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_UniformDiscreteness_FgOfUnifDiscrete
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_TBDisc
import Theorems.Thm_PI_UnitaryGroupMassFormula_TBDisc_fGOfDisc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : ReciprocityTheory.ChartRestriction.G.TB.FGOfDiscSt :=
  PI.UnitaryGroupMassFormula.TBDisc.fGOfDisc
