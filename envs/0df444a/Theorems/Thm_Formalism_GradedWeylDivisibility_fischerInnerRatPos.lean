-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_fischerInnerRatPos
-- name    : Formalism.GradedWeylDivisibility.fischerInnerRatPos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:39.36097+00:00
-- url     : https://prove2.me/theorems/aa88a064-9b7f-4f3b-9fac-0519e3823b55
-- title:
--   Graded Weyl Divisibility: fischer Inner Rat Pos
-- statement:
--   The Graded Weyl Divisibility construction uses the fischer Inner Rat Pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockQPos.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockQPos.lean#L10-L11

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.fischerInnerRatPos : FockQPos := by sorry
