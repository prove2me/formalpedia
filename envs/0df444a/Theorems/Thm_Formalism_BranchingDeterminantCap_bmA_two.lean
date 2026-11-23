-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_two
-- name    : Formalism.BranchingDeterminantCap.bmA_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:20:36.457593+00:00
-- url     : https://prove2.me/theorems/623e573b-e3b4-41c0-a7c4-c0a5e2b96d9c
-- title:
--   Branching Determinant Cap: bm A two
-- statement:
--   The Branching Determinant Cap construction uses the bm A two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L587-L594
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L587-L594

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
variable {A : Type*} [Ring A]

theorem Formalism.BranchingDeterminantCap.bmA_two (c X Y : A) (hX : c * X = X * c) (hY : c * Y = Y * c) (P Q : Prop) [Decidable P] [Decidable Q] :
    ((if P then c else 0) - X) * ((if Q then c + 1 else 0) - Y) -
        ((if Q then c else 0) - Y) * ((if P then c + 1 else 0) - X) =
      (if P then Y else 0) - (if Q then X else 0) + (X * Y - Y * X) := by sorry
