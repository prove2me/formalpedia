-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmD_nil
-- name    : Formalism.BranchingDeterminantCap.bmD_nil
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:20:45.84184+00:00
-- url     : https://prove2.me/theorems/9f06649a-625d-4957-8b33-f989d47b292b
-- title:
--   Branching Determinant Cap: bm D nil
-- statement:
--   The Branching Determinant Cap construction uses the bm D nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1440-L1475
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1440-L1475

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

theorem Formalism.BranchingDeterminantCap.bmD_nil {R : Type} [CommRing R] [IsDomain R] [CharZero R] {r n : ℕ} (lam : Fin n → ℕ)
    (G : MvPolynomial (Fin r × Fin n) R) (hG : G ∈ dualWeyl R r n lam) (l j : Fin n) (hlj : l < j)
    (k : ℕ) (hk : (lam l : ℤ) - (lam j : ℤ) < (k : ℤ)) : (ndF R r n l j)^[k] G = 0 := by sorry
