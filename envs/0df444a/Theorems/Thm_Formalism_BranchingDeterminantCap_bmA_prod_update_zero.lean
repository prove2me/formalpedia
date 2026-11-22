-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_prod_update_zero
-- name    : Formalism.BranchingDeterminantCap.bmA_prod_update_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:01:44.41813+00:00
-- url     : https://prove2.me/theorems/b41ba8a3-5ecd-4d45-9010-78c1d23642cb
-- title:
--   Branching Determinant Cap: bm A prod update zero
-- statement:
--   The Branching Determinant Cap construction uses the bm A prod update zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L508-L510
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L508-L510

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

theorem Formalism.BranchingDeterminantCap.bmA_prod_update_zero {n : ℕ} (g : Fin (n + 1) → A) (w : A) :
    (List.ofFn (Function.update g 0 w)).prod = w * (List.ofFn fun i : Fin n => g i.succ).prod := by sorry
