-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_apply_le_of_norm_le
-- name    : Formalism.BranchingDeterminantCap.PrismTransfer.apply_le_of_norm_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:20:57.945871+00:00
-- url     : https://prove2.me/theorems/0e8e9abe-2d74-4ce4-9426-4173cbd1d695
-- title:
--   Prism Transfer: apply le of norm le
-- statement:
--   The Prism Transfer construction uses the apply le of norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L105-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L105-L112

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

theorem Formalism.BranchingDeterminantCap.PrismTransfer.apply_le_of_norm_le (M : Matrix ι ι ℂ)
    (hM : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖ ≤ 1)
    (z : EuclideanSpace ℂ ι) : ‖Matrix.toEuclideanLin M z‖ ≤ ‖z‖ := by sorry
