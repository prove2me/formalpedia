-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_mul_blockDiag_apply
-- name    : Formalism.BranchingDeterminantCap.PrismTransfer.mul_blockDiag_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:19:23.572234+00:00
-- url     : https://prove2.me/theorems/678e78f3-a33b-4762-a428-cb846ab2f755
-- title:
--   Prism Transfer: mul block Diag apply
-- statement:
--   The Prism Transfer construction uses the mul block Diag apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L191-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L191-L199

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

theorem Formalism.BranchingDeterminantCap.PrismTransfer.mul_blockDiag_apply {n : ℕ} {κ : Type} (N : Matrix κ (Σ _ : Fin n, ι) ℂ) (Y : Matrix ι ι ℂ)
    (k : κ) (i : Fin n) (j : ι) :
    (N * Matrix.blockDiagonal' (fun _ : Fin n => Y)) k ⟨i, j⟩ = ∑ l, N k ⟨i, l⟩ * Y l j := by sorry
