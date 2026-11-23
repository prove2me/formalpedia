-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_opNormAt_colMap
-- name    : Formalism.BranchingDeterminantCap.PrismTransfer.opNormAt_colMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:22:08.683609+00:00
-- url     : https://prove2.me/theorems/0d2f542f-5165-4dd6-9f40-6f0760c916b7
-- title:
--   Prism Transfer: op Norm At col Map
-- statement:
--   The Prism Transfer construction uses the op Norm At col Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L273-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L273-L291

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

theorem Formalism.BranchingDeterminantCap.PrismTransfer.opNormAt_colMap {n : ℕ} (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (G : ℕ) (x : Fin n → V →ₗ[K] V) (v : InfinitePlace K)
    (hx : ∀ i, opNormAt b X b X v (x i) ≤ 1) :
    opNormAt b X (Pi.basis fun _ : Fin n => b) (fun v => Matrix.blockDiagonal' fun _ : Fin n => X v) v
      (colMap ((G : K) ^ 3) x) ≤ (G : ℝ) ^ 3 * Real.sqrt n := by sorry
