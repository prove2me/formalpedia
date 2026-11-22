-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_extendMatrix_last_right_zero
-- name    : Formalism.BranchingDeterminantCap.extendMatrix_last_right_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:23:53.656549+00:00
-- url     : https://prove2.me/theorems/10b24ed3-b117-415d-821e-510bcb4af804
-- title:
--   Branching Determinant Cap: extend Matrix last right zero
-- statement:
--   The Branching Determinant Cap construction uses the extend Matrix last right zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L347-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L347-L349

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

theorem Formalism.BranchingDeterminantCap.extendMatrix_last_right_zero (R : Type*) [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R)
    (a : Fin (n + 1)) (ha : a ≠ Fin.last n) : extM R g a (Fin.last n) = 0 := by sorry
