-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_toMatrix_rowMap
-- name    : Formalism.BranchingDeterminantCap.PrismTransfer.toMatrix_rowMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:19:39.354332+00:00
-- url     : https://prove2.me/theorems/fb8b140b-6e18-4bc8-b35e-c097e7d68a2b
-- title:
--   Prism Transfer: to Matrix row Map
-- statement:
--   The Prism Transfer construction uses the to Matrix row Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L236-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L236-L247

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

theorem Formalism.BranchingDeterminantCap.PrismTransfer.toMatrix_rowMap {n : ℕ} (b : Basis ι K V) (c : K) (x : Fin n → V →ₗ[K] V) (k : ι)
    (i : Fin n) (j : ι) :
    LinearMap.toMatrix (Pi.basis fun _ : Fin n => b) b (rowMap c x) k ⟨i, j⟩ =
      c * LinearMap.toMatrix b b (x i) k j := by sorry
