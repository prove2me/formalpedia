-- Prove2me | solution 1 for qnRuleRight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:07:47.553403+00:00
-- url     : https://prove2.me/submissions/11847d83-4930-447f-94e0-dfbd04dae02d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_EllSingleZero
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnRuleRight
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_ruleRight_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : Formalism.FourierDecayAlt.Q.RuleRight := Formalism.FourierDecayAlt.Q.QRR.ruleRight_main
