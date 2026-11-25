-- Prove2me | solution 1 for qnRuleLeft
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:07:46.033191+00:00
-- url     : https://prove2.me/submissions/92efa5dd-db35-4859-99cd-8d3c770f6d27

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_LeftMultiplicationRule
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnRuleLeft
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_left_multiplication_rule


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : Formalism.FourierDecayAlt.Q.RuleLeft := Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.left_multiplication_rule
