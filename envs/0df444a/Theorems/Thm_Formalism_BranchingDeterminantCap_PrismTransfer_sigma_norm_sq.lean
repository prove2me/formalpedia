-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_sigma_norm_sq
-- name    : Formalism.BranchingDeterminantCap.PrismTransfer.sigma_norm_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:21:38.978808+00:00
-- url     : https://prove2.me/theorems/b500d6be-c4b3-4086-8b18-cd86f72576ac
-- title:
--   Prism Transfer: sigma norm sq
-- statement:
--   The Prism Transfer construction uses the sigma norm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L98-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L98-L103

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

theorem Formalism.BranchingDeterminantCap.PrismTransfer.sigma_norm_sq {n : ℕ} (z : EuclideanSpace ℂ (Σ _ : Fin n, ι)) :
    ‖z‖ ^ 2 = ∑ i, ‖(WithLp.toLp 2 (fun j => z ⟨i, j⟩) : EuclideanSpace ℂ ι)‖ ^ 2 := by sorry
