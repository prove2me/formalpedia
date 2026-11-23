-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_rowAct_low
-- name    : Formalism.BranchingDeterminantCap.bmF_rowAct_low
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:23:42.67008+00:00
-- url     : https://prove2.me/theorems/9eb8ed26-7f57-477f-a264-e451695c0cef
-- title:
--   Branching Determinant Cap: bm F row Act low
-- statement:
--   The Branching Determinant Cap construction uses the bm F row Act low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1960-L1969
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1960-L1969

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

theorem Formalism.BranchingDeterminantCap.bmF_rowAct_low (R : Type*) [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R) (D : ℤ) (L : BP R n)
    (hL : IsLow D L) : IsLow D (rowAct R (extM R g) L) := by sorry
