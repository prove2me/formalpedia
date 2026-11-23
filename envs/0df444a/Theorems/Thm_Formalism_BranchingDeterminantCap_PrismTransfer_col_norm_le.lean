-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_col_norm_le
-- name    : Formalism.BranchingDeterminantCap.PrismTransfer.col_norm_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:19:45.416739+00:00
-- url     : https://prove2.me/theorems/20dbb4cb-5fa0-4870-970c-18175965425c
-- title:
--   Prism Transfer: col norm le
-- statement:
--   The Prism Transfer construction uses the col norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L147-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L147-L174

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
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem Formalism.BranchingDeterminantCap.PrismTransfer.col_norm_le {n : ℕ} (M : Fin n → Matrix ι ι ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hM : ∀ i, ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (M i))‖ ≤ 1)
    (C : Matrix (Σ _ : Fin n, ι) ι ℂ) (hC : ∀ p k, C p k = (c : ℂ) * M p.1 p.2 k) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin C)‖ ≤ c * Real.sqrt n := by sorry
