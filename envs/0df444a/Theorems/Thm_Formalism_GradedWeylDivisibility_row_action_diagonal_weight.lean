-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_row_action_diagonal_weight
-- name    : Formalism.GradedWeylDivisibility.row_action_diagonal_weight
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:53.212803+00:00
-- url     : https://prove2.me/theorems/b95d0c3b-b74d-4cb5-ac04-f130accdda9f
-- title:
--   Graded Weyl Divisibility: row action diagonal weight
-- statement:
--   The Graded Weyl Divisibility construction uses the row action diagonal weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/RowActDiagWeight.lean#L10-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/RowActDiagWeight.lean#L10-L45

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowActDiagWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.row_action_diagonal_weight : RowActDiagWeight := by sorry
