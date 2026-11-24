-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmD_weight
-- name    : Formalism.BranchingDeterminantCap.bmD_weight
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:20:32.477983+00:00
-- url     : https://prove2.me/theorems/95619eec-e76e-4ad4-86a6-b9ec968e4e00
-- title:
--   Branching Determinant Cap: bm D weight
-- statement:
--   The Branching Determinant Cap construction uses the bm D weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1425-L1438
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1425-L1438

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

theorem Formalism.BranchingDeterminantCap.bmD_weight {R : Type} [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (lam : Fin n → ℕ)
    (G : BP R n) (hG : G ∈ dualWeyl R (n + 1) n lam) (β : Fin n → ℤ) (s : Fin n) :
    bmE R n s s (zcomp R n β G) = (((lam s : ℤ) - β s : ℤ) : R) • zcomp R n β G := by sorry
