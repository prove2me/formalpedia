-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_central
-- name    : Formalism.BranchingDeterminantCap.bmK_central
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:23:01.98995+00:00
-- url     : https://prove2.me/theorems/34cb53fc-a92f-434f-bfdc-6c44496592d1
-- title:
--   Branching Determinant Cap: bm K central
-- statement:
--   The Branching Determinant Cap construction uses the bm K central property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2399-L2401
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2399-L2401

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

theorem Formalism.BranchingDeterminantCap.bmK_central (R : Type*) [CommRing R] [IsDomain R] [CharZero R] (n : ℕ) (k l : Fin n) (u : ℤ) :
    Commute (bmEL R n k l) (bmCap R n u) := by sorry
