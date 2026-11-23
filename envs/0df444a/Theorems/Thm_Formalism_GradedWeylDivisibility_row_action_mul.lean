-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_row_action_mul
-- name    : Formalism.GradedWeylDivisibility.row_action_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:00.682071+00:00
-- url     : https://prove2.me/theorems/3a12f304-fb04-406c-a7b2-111878a46238
-- title:
--   Graded Weyl Divisibility: row action mul
-- statement:
--   The Graded Weyl Divisibility construction uses the row action mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/RowActMul.lean#L9-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/RowActMul.lean#L9-L15

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowActMul
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

theorem Formalism.GradedWeylDivisibility.row_action_mul : RowActMul := by sorry
