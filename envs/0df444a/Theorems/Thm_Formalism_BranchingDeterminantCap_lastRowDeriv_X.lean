-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_lastRowDeriv_X
-- name    : Formalism.BranchingDeterminantCap.lastRowDeriv_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:24:30.99593+00:00
-- url     : https://prove2.me/theorems/5e77db2c-cfc3-4fdf-8c0e-fbadb9e5b750
-- title:
--   Branching Determinant Cap: last Row Deriv X
-- statement:
--   The Branching Determinant Cap construction uses the last Row Deriv X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L274-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L274-L277

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

theorem Formalism.BranchingDeterminantCap.lastRowDeriv_X (R : Type*) [CommRing R] (n : ℕ) (s t : Fin n) (v : Fin (n + 1) × Fin n) :
    bmZ R n s t (X v) = if v.2 = t ∧ v.1 = Fin.last n then X (v.1, s) else 0 := by sorry
