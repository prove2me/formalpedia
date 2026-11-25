-- Prove2me | solution 1 for qnRdSkew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:29:53.50933+00:00
-- url     : https://prove2.me/submissions/347186fe-cf79-4806-900a-5e915634b6d5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_SkewReductionGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_Analytic
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnRdSkew
import Theorems.Thm_QnRdSkewW_rdSkew_of
import Theorems.Thm_QnRdSkewW_skew_reduction_analytic
import Theorems.Thm_QnRdSkewW_skew_reduction_group


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : Formalism.FourierDecayAlt.Q.RdSkew :=
  QnRdSkewW.rdSkew_of QnRdSkewW.skew_reduction_group QnRdSkewW.skew_reduction_analytic
