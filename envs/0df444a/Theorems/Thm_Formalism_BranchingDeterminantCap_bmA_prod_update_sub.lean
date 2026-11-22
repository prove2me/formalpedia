-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_prod_update_sub
-- name    : Formalism.BranchingDeterminantCap.bmA_prod_update_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:22:19.282497+00:00
-- url     : https://prove2.me/theorems/fa6a0c5f-1bbf-4449-9b0d-daa4fe2b5b87
-- title:
--   Branching Determinant Cap: bm A prod update sub
-- statement:
--   The Branching Determinant Cap construction uses the bm A prod update sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L571-L579
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L571-L579

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

theorem Formalism.BranchingDeterminantCap.bmA_prod_update_sub {n : ℕ} (g : Fin n → A) (k : Fin n) (a b : A) :
    (List.ofFn (Function.update g k (a - b))).prod =
      (List.ofFn (Function.update g k a)).prod - (List.ofFn (Function.update g k b)).prod := by sorry
