-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_blockDiag_det
-- name    : Formalism.BranchingDeterminantCap.PrismTransfer.blockDiag_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:20:55.114718+00:00
-- url     : https://prove2.me/theorems/86d474b9-7ee8-426f-82c5-08649f44216b
-- title:
--   Prism Transfer: block Diag det
-- statement:
--   The Prism Transfer construction uses the block Diag det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L185-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L185-L186

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

theorem Formalism.BranchingDeterminantCap.PrismTransfer.blockDiag_det {n : ℕ} (Y : Matrix ι ι ℂ) (hY : IsUnit Y.det) :
    IsUnit (Matrix.blockDiagonal' (fun _ : Fin n => Y)).det := by sorry
