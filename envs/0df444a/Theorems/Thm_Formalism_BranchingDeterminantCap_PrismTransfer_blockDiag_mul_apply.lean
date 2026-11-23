-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_blockDiag_mul_apply
-- name    : Formalism.BranchingDeterminantCap.PrismTransfer.blockDiag_mul_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:19:11.230909+00:00
-- url     : https://prove2.me/theorems/f2c79fe2-73cc-42c6-84d7-a87823e137bc
-- title:
--   Prism Transfer: block Diag mul apply
-- statement:
--   The Prism Transfer construction uses the block Diag mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L201-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L201-L209

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

theorem Formalism.BranchingDeterminantCap.PrismTransfer.blockDiag_mul_apply {n : ℕ} {κ : Type} (N : Matrix (Σ _ : Fin n, ι) κ ℂ) (Y : Matrix ι ι ℂ)
    (k : κ) (i : Fin n) (j : ι) :
    (Matrix.blockDiagonal' (fun _ : Fin n => Y) * N) ⟨i, j⟩ k = ∑ l, Y j l * N ⟨i, l⟩ k := by sorry
