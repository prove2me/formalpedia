-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_one
-- name    : Formalism.BranchingDeterminantCap.bmLift_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:02:28.297807+00:00
-- url     : https://prove2.me/theorems/d90045e1-8ee4-47f1-b490-6384a64102c3
-- title:
--   Branching Determinant Cap: bm Lift one
-- statement:
--   The Branching Determinant Cap construction uses the bm Lift one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1743-L1754
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1743-L1754

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

theorem Formalism.BranchingDeterminantCap.bmLift_one (R : Type*) [CommRing R] (n : ℕ) : bmLift R n 0 0 1 1 := by sorry
