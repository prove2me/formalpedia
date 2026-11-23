-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_row_zero
-- name    : Formalism.BranchingDeterminantCap.bmA_row_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:20:27.734796+00:00
-- url     : https://prove2.me/theorems/bda693fa-3935-4676-ac70-63e0326e989a
-- title:
--   Branching Determinant Cap: bm A row zero
-- statement:
--   The Branching Determinant Cap construction uses the bm A row zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L739-L758
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L739-L758

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
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}

theorem Formalism.BranchingDeterminantCap.bmA_row_zero (E : Fin n → Fin n → Module.End R M) (u : ℤ)
    (h2 : ∀ x : Module.End R M, x + x = 0 → x = 0) (c β : Fin n → Fin n) (k l : Fin n) (hkl : k ≠ l)
    (hc : c k = c l) :
    ∑ α : Equiv.Perm (Fin n), ((Equiv.Perm.sign α : ℤˣ) : ℤ) • bmM E u (c ∘ α) β = 0 := by sorry
