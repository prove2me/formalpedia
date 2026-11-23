-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_comm_prod
-- name    : Formalism.BranchingDeterminantCap.bmA_comm_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:19:34.630274+00:00
-- url     : https://prove2.me/theorems/ddd53a2d-5ea2-4865-adfb-e3ba21a143f3
-- title:
--   Branching Determinant Cap: bm A comm prod
-- statement:
--   The Branching Determinant Cap construction uses the bm A comm prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L525-L534
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L525-L534

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

theorem Formalism.BranchingDeterminantCap.bmA_comm_prod (x : A) : ∀ {n : ℕ} (g : Fin n → A),
    x * (List.ofFn g).prod - (List.ofFn g).prod * x =
      ∑ k, (List.ofFn (Function.update g k (x * g k - g k * x))).prod
  := by sorry
