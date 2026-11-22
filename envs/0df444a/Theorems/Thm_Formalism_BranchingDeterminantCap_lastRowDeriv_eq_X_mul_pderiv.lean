-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_lastRowDeriv_eq_X_mul_pderiv
-- name    : Formalism.BranchingDeterminantCap.lastRowDeriv_eq_X_mul_pderiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:24:59.6138+00:00
-- url     : https://prove2.me/theorems/99855129-d4c5-4734-8e60-53c0068a9a66
-- title:
--   Branching Determinant Cap: last Row Deriv eq X mul pderiv
-- statement:
--   The Branching Determinant Cap construction uses the last Row Deriv eq X mul pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L398-L405
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L398-L405

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

theorem Formalism.BranchingDeterminantCap.lastRowDeriv_eq_X_mul_pderiv (R : Type*) [CommRing R] (n : ℕ) (s t : Fin n) (F : BP R n) :
    bmZ R n s t F = X (Fin.last n, s) * pderiv (Fin.last n, t) F := by sorry
