-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_toMatrix_colMap
-- name    : Formalism.BranchingDeterminantCap.PrismTransfer.toMatrix_colMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:19:10.402805+00:00
-- url     : https://prove2.me/theorems/c054ce46-e17a-4c6b-ac01-39462e284fd2
-- title:
--   Prism Transfer: to Matrix col Map
-- statement:
--   The Prism Transfer construction uses the to Matrix col Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L249-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L249-L253

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

theorem Formalism.BranchingDeterminantCap.PrismTransfer.toMatrix_colMap {n : ℕ} (b : Basis ι K V) (c : K) (x : Fin n → V →ₗ[K] V) (k : ι)
    (i : Fin n) (j : ι) :
    LinearMap.toMatrix b (Pi.basis fun _ : Fin n => b) (colMap c x) ⟨i, j⟩ k =
      c * LinearMap.toMatrix b b (x i) j k := by sorry
