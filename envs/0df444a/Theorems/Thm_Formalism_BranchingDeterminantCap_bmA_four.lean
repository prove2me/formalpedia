-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_four
-- name    : Formalism.BranchingDeterminantCap.bmA_four
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:19:46.699807+00:00
-- url     : https://prove2.me/theorems/eca680e7-a745-49bf-b58a-600d325cfbfb
-- title:
--   Branching Determinant Cap: bm A four
-- statement:
--   The Branching Determinant Cap construction uses the bm A four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L619-L646
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L619-L646

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

theorem Formalism.BranchingDeterminantCap.bmA_four (E : Fin n → Fin n → Module.End R M) (u : ℤ)
    (hE : ∀ i j k l, E i j * E k l - E k l * E i j = (if j = k then E i l else 0) - (if i = l then E k j else 0))
    (p p' : Fin n) (hp : p'.val = p.val + 1) (α β : Fin n → Fin n) :
    bmM E u α β - bmM E u (α ∘ Equiv.swap p p') (β ∘ Equiv.swap p p') =
      bmM E u (α ∘ Equiv.swap p p') β - bmM E u α (β ∘ Equiv.swap p p') := by sorry
