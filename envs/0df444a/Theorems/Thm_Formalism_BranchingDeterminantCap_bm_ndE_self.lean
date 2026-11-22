-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bm_ndE_self
-- name    : Formalism.BranchingDeterminantCap.bm_ndE_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:23:30.224635+00:00
-- url     : https://prove2.me/theorems/024c5f7e-25d1-46c3-a8c7-446347efc35c
-- title:
--   Branching Determinant Cap: bm nd E self
-- statement:
--   The Branching Determinant Cap construction uses the bm nd E self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L328-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L328-L334

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

theorem Formalism.BranchingDeterminantCap.bm_ndE_self (R : Type*) [CommRing R] (r n : ℕ) (s : Fin n) : ndE R r n s s = ndEul R r n s := by sorry
