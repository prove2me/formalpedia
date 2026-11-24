-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_leadj_star_ratCast
-- name    : Formalism.GradedWeylDivisibility.leadj_star_ratCast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:57.644117+00:00
-- url     : https://prove2.me/theorems/1e1ec864-57f2-4502-becf-0f3e819e0443
-- title:
--   Graded Weyl Divisibility: leadj star rat Cast
-- statement:
--   The Graded Weyl Divisibility construction uses the leadj star rat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockQRowAct.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockQRowAct.lean#L9-L10

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.REAL
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.leadj_star_ratCast (q : ℚ) : star ((q : ℂ)) = (q : ℂ) := by sorry
