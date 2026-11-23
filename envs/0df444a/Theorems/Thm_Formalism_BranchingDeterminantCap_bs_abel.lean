-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bs_abel
-- name    : Formalism.BranchingDeterminantCap.bs_abel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:25:51.481932+00:00
-- url     : https://prove2.me/theorems/c89821b1-1f7a-480c-babe-71cac192bc3b
-- title:
--   Branching Determinant Cap: bs abel
-- statement:
--   The Branching Determinant Cap construction uses the bs abel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L87-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L87-L113

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
open Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap

theorem Formalism.BranchingDeterminantCap.bs_abel (n : ℕ) (x : Fin n → ℤ) :
    ∑ a, (a.val : ℤ) * x a =
      ∑ k ∈ Finset.range n, ((∑ a, x a) - ∑ a : Fin n with a.val < k + 1, x a) := by sorry
