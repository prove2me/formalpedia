-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_columnLexBideterminant_of_initialMinor
-- name    : Formalism.GradedWeylDivisibility.columnLexBideterminant_of_initialMinor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:55.845049+00:00
-- url     : https://prove2.me/theorems/3a2c916a-659a-4c92-aac8-66584625ece6
-- title:
--   Graded Weyl Divisibility: column Lex Bideterminant of initial Minor
-- statement:
--   The Graded Weyl Divisibility construction uses the column Lex Bideterminant of initial Minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/ColumnLexBideterminant.lean#L11-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/ColumnLexBideterminant.lean#L11-L27

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ColumnLexBideterminant
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

theorem Formalism.GradedWeylDivisibility.columnLexBideterminant_of_initialMinor (h : ColLexInitMinor) : ColumnLexBideterminant := by sorry
