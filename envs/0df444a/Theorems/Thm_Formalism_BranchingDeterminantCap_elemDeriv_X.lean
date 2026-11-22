-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_elemDeriv_X
-- name    : Formalism.BranchingDeterminantCap.elemDeriv_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:39:15.746677+00:00
-- url     : https://prove2.me/theorems/89af6a15-17a5-4e8a-a61d-da21d30c0fbe
-- title:
--   Branching Determinant Cap: elem Deriv X
-- statement:
--   The Branching Determinant Cap construction uses the elem Deriv X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L269-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L269-L272

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

theorem Formalism.BranchingDeterminantCap.elemDeriv_X (R : Type*) [CommRing R] (n : ℕ) (s t : Fin n) (v : Fin (n + 1) × Fin n) :
    bmE R n s t (X v) = if v.2 = t ∧ v.1 ≠ Fin.last n then X (v.1, s) else 0 := by sorry
