-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bm_isLow_iff
-- name    : Formalism.BranchingDeterminantCap.bm_isLow_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:23:04.600559+00:00
-- url     : https://prove2.me/theorems/e4d82d45-2dab-42e5-ba52-f018f359a45a
-- title:
--   Branching Determinant Cap: bm is Low iff
-- statement:
--   The Branching Determinant Cap construction uses the bm is Low iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1588-L1606
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1588-L1606

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

theorem Formalism.BranchingDeterminantCap.bm_isLow_iff {R : Type*} [CommRing R] {n : ℕ} (D : ℤ) (L : BP R n) :
    IsLow D L ↔ ∀ β, D ≤ omg β → zcomp R n β L = 0 := by sorry
