-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bs_height_le
-- name    : Formalism.BranchingDeterminantCap.bs_height_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:25:54.68362+00:00
-- url     : https://prove2.me/theorems/3e45090f-2c9d-4ff2-9af8-0b0a1092f720
-- title:
--   Branching Determinant Cap: bs height le
-- statement:
--   The Branching Determinant Cap construction uses the bs height le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L115-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L115-L125

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

theorem Formalism.BranchingDeterminantCap.bs_height_le (n : ℕ) (x y : Fin n → ℕ)
    (h1 : ∀ k : ℕ, (∑ a : Fin n with a.val < k, x a) ≤ ∑ a : Fin n with a.val < k, y a)
    (h2 : ∑ a, x a = ∑ a, y a) :
    ∑ a : Fin n, (a.val : ℤ) * (y a : ℤ) ≤ ∑ a : Fin n, (a.val : ℤ) * (x a : ℤ) := by sorry
