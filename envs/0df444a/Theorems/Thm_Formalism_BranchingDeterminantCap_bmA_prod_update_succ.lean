-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_prod_update_succ
-- name    : Formalism.BranchingDeterminantCap.bmA_prod_update_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:01:33.957002+00:00
-- url     : https://prove2.me/theorems/5953aca1-72d5-474c-b78d-84f3b3ca2bf3
-- title:
--   Branching Determinant Cap: bm A prod update succ
-- statement:
--   The Branching Determinant Cap construction uses the bm A prod update succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L512-L523
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L512-L523

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

theorem Formalism.BranchingDeterminantCap.bmA_prod_update_succ {n : ℕ} (g : Fin (n + 1) → A) (k : Fin n) (w : A) :
    (List.ofFn (Function.update g k.succ w)).prod =
      g 0 * (List.ofFn (Function.update (fun i : Fin n => g i.succ) k w)).prod := by sorry
