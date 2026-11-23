-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmZL_comm_bmEL
-- name    : Formalism.BranchingDeterminantCap.bmZL_comm_bmEL
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:47.681661+00:00
-- url     : https://prove2.me/theorems/a311d089-8eb0-4617-9dec-d83e2ef8ef17
-- title:
--   Branching Determinant Cap: bm ZL comm bm EL
-- statement:
--   The Branching Determinant Cap construction uses the bm ZL comm bm EL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L340-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L340-L345

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap

theorem Formalism.BranchingDeterminantCap.bmZL_comm_bmEL (R : Type*) [CommRing R] (n : ℕ) (l j s t : Fin n) :
    Commute (bmZL R n l j) (bmEL R n s t) := by sorry
