-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_log_bound
-- name    : Formalism.BranchingDeterminantCap.PrismTransfer.log_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:21:29.825584+00:00
-- url     : https://prove2.me/theorems/2230081c-2083-46ae-aab4-937b790b0be6
-- title:
--   Prism Transfer: log bound
-- statement:
--   The Prism Transfer construction uses the log bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L324-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L324-L339

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Transfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.HN
open PrismTransfer
open Formalism.BranchingDeterminantCap.PrismTransfer
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
variable {W κ : Type} [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ]

theorem Formalism.BranchingDeterminantCap.PrismTransfer.log_bound (G n : ℕ) (hG : 0 < G) (hn : 0 < n) :
    1 ≤ (G : ℝ) ^ 3 * Real.sqrt n ∧
      2 * Real.log ((G : ℝ) ^ 3 * Real.sqrt n) = 6 * Real.log G + Real.log n := by sorry
