-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_D_zero
-- name    : Formalism.BranchingDeterminantCap.bmG_D_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:23:17.36761+00:00
-- url     : https://prove2.me/theorems/fae92a43-3b22-4016-a5c0-bcf5b83c63ab
-- title:
--   Branching Determinant Cap: bm G D zero
-- statement:
--   The Branching Determinant Cap construction uses the bm G D zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2251-L2252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2251-L2252

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

theorem Formalism.BranchingDeterminantCap.bmG_D_zero (R : Type*) [CommRing R] (n : ℕ) : bmG_D R n 0 = 1 := by sorry
