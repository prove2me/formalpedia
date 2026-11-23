-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmD_raise
-- name    : Formalism.BranchingDeterminantCap.bmD_raise
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:20:43.91149+00:00
-- url     : https://prove2.me/theorems/1c0282ee-901f-452e-a086-26c9a8f96677
-- title:
--   Branching Determinant Cap: bm D raise
-- statement:
--   The Branching Determinant Cap construction uses the bm D raise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1409-L1423
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1409-L1423

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

theorem Formalism.BranchingDeterminantCap.bmD_raise {R : Type} [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (lam : Fin n → ℕ)
    (G : BP R n) (hG : G ∈ dualWeyl R (n + 1) n lam) (β : Fin n → ℤ)
    (hmax : ∀ β', zcomp R n β' G ≠ 0 → omg β' ≤ omg β) (l j : Fin n) (hlj : l < j) :
    bmE R n l j (zcomp R n β G) = 0 := by sorry
