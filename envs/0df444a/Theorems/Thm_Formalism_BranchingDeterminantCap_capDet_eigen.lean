-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_capDet_eigen
-- name    : Formalism.BranchingDeterminantCap.capDet_eigen
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:24:02.221468+00:00
-- url     : https://prove2.me/theorems/3c830e49-9458-43b8-b4dc-d7978f1d0571
-- title:
--   Branching Determinant Cap: cap Det eigen
-- statement:
--   The Branching Determinant Cap construction uses the cap Det eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L887-L916
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L887-L916

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
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}

theorem Formalism.BranchingDeterminantCap.capDet_eigen {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (E : Fin n → Fin n → Module.End R M) (u : ℤ) (v : M) (μ : Fin n → ℤ)
    (hr : ∀ l j, l < j → E l j v = 0) (hw : ∀ s, E s s v = ((μ s : ℤ) : R) • v) :
    capDet E u v = ((∏ j : Fin n, (u + ((j : ℕ) : ℤ) - μ j) : ℤ) : R) • v := by sorry
