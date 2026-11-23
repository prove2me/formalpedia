-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_adj
-- name    : Formalism.BranchingDeterminantCap.bmA_adj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:19:25.375951+00:00
-- url     : https://prove2.me/theorems/325bf0a6-e8e5-4427-949c-f0945d759a6c
-- title:
--   Branching Determinant Cap: bm A adj
-- statement:
--   The Branching Determinant Cap construction uses the bm A adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L536-L569
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L536-L569

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
variable {A : Type*} [Ring A]

theorem Formalism.BranchingDeterminantCap.bmA_adj : ∀ {n : ℕ} (g : Fin n → A) (p p' : Fin n), p'.val = p.val + 1 →
    ∃ L Rr : A, ∀ a b : A,
      (List.ofFn (Function.update (Function.update g p a) p' b)).prod = L * (a * b) * Rr
  := by sorry
