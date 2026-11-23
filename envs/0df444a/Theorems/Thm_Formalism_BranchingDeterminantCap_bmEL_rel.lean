-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmEL_rel
-- name    : Formalism.BranchingDeterminantCap.bmEL_rel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:20:43.948233+00:00
-- url     : https://prove2.me/theorems/0ee70554-45a5-44f3-a46b-55f8a480ec7c
-- title:
--   Branching Determinant Cap: bm EL rel
-- statement:
--   The Branching Determinant Cap construction uses the bm EL rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L304-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L304-L312

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

theorem Formalism.BranchingDeterminantCap.bmEL_rel (R : Type*) [CommRing R] (n : ℕ) (i j k l : Fin n) :
    bmEL R n i j * bmEL R n k l - bmEL R n k l * bmEL R n i j =
      (if j = k then bmEL R n i l else 0) - (if i = l then bmEL R n k j else 0) := by sorry
