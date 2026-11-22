-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_columnSums_holds
-- name    : Formalism.GradedWeylDivisibility.columnSums_holds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:10:32.10836+00:00
-- url     : https://prove2.me/theorems/76eb35ec-c459-463a-9865-5acd54f90e73
-- title:
--   Graded Weyl Divisibility: column Sums holds
-- statement:
--   The Graded Weyl Divisibility construction uses the column Sums holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/ColSums.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/ColSums.lean#L17-L21

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ColSums
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

theorem Formalism.GradedWeylDivisibility.columnSums_holds : ColSums := by sorry
