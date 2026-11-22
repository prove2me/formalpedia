-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_blockDiag_mul_inv
-- name    : Formalism.BranchingDeterminantCap.PrismTransfer.blockDiag_mul_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:21:43.339515+00:00
-- url     : https://prove2.me/theorems/09a08e7f-3401-4962-9158-053a7c6fee36
-- title:
--   Prism Transfer: block Diag mul inv
-- statement:
--   The Prism Transfer construction uses the block Diag mul inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L176-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L176-L183

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

theorem Formalism.BranchingDeterminantCap.PrismTransfer.blockDiag_mul_inv {n : ℕ} (Y : Matrix ι ι ℂ) (hY : IsUnit Y.det) :
    Matrix.blockDiagonal' (fun _ : Fin n => Y) * Matrix.blockDiagonal' (fun _ : Fin n => Y⁻¹) = 1 := by sorry
