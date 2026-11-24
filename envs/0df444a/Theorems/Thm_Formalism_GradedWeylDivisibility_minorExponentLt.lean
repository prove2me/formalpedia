-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_minorExponentLt
-- name    : Formalism.GradedWeylDivisibility.minorExponentLt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:23:23.344606+00:00
-- url     : https://prove2.me/theorems/e1d68eb4-d22e-4d91-9793-e08bf90041f1
-- title:
--   Graded Weyl Divisibility: minor Exponent Lt
-- statement:
--   The Graded Weyl Divisibility construction uses the minor Exponent Lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/MinorExpLt.lean#L102-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/MinorExpLt.lean#L102-L154

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_MinorExpLt
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
open scoped MonomialOrder

theorem Formalism.GradedWeylDivisibility.minorExponentLt : MinorExpLt := by sorry
