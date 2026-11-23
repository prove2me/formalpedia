-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_tri
-- name    : Formalism.BranchingDeterminantCap.bmA_tri
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:20:39.430874+00:00
-- url     : https://prove2.me/theorems/cd29e45d-0ace-4859-b0fc-3216b1abf024
-- title:
--   Branching Determinant Cap: bm A tri
-- statement:
--   The Branching Determinant Cap construction uses the bm A tri property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L859-L885
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L859-L885

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod

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

theorem Formalism.BranchingDeterminantCap.bmA_tri (v : M) : ∀ {m : ℕ} (g : Fin m → Module.End R M) (c : Fin m → R) (F : Fin m → Prop),
    (∀ k, F k → g k v = c k • v) → (∀ k, ¬ F k → (∀ j, k < j → F j) → g k v = 0) →
    ((∀ k, F k) → (List.ofFn g).prod v = (∏ k, c k) • v) ∧ ((¬ ∀ k, F k) → (List.ofFn g).prod v = 0)
  := by sorry
