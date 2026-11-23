-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_low_smul
-- name    : Formalism.BranchingDeterminantCap.bmF_low_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:07.311877+00:00
-- url     : https://prove2.me/theorems/9ad6996e-c9e8-4fb8-9948-a0bc4e20848b
-- title:
--   Branching Determinant Cap: bm F low smul
-- statement:
--   The Branching Determinant Cap construction uses the bm F low smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1619-L1622
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1619-L1622

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

theorem Formalism.BranchingDeterminantCap.bmF_low_smul {R : Type*} [CommRing R] {n : ℕ} {D : ℤ} {L : BP R n} (c : R) (h : IsLow D L) :
    IsLow D (c • L) := by sorry
