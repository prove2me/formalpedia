-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_one_sub_sum_le_prod
-- name    : Formalism.BranchingDeterminantCap.one_sub_sum_le_prod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:26:40.255797+00:00
-- url     : https://prove2.me/theorems/ec9f1028-88de-4164-b361-d2021e54b9d4
-- title:
--   Branching Determinant Cap: one sub sum le prod
-- statement:
--   The Branching Determinant Cap construction uses the one sub sum le prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Numeric.lean#L88-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Numeric.lean#L88-L101

import Definitions.Def_Formalism_BranchSandwichDivisors_NormLog
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Interlace
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Numeric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.BranchingDeterminantCap

theorem Formalism.BranchingDeterminantCap.one_sub_sum_le_prod {ι : Type} (s : Finset ι) (x : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ x i)
    (h1 : ∀ i ∈ s, x i ≤ 1) : 1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by sorry
