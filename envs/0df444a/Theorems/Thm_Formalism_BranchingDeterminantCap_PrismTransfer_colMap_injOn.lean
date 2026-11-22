-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_colMap_injOn
-- name    : Formalism.BranchingDeterminantCap.PrismTransfer.colMap_injOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:21:28.208249+00:00
-- url     : https://prove2.me/theorems/638621fa-ba66-4aac-b08e-11aa517fdb78
-- title:
--   Prism Transfer: col Map inj On
-- statement:
--   The Prism Transfer construction uses the col Map inj On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L369-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L369-L377

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
  {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]

theorem Formalism.BranchingDeterminantCap.PrismTransfer.colMap_injOn {n : ℕ} (G : ℕ) (hG : 0 < G) (xs : Fin n → V →ₗ[K] V) (B : Submodule (𝓞 K) V)
    (h : ∀ c ∈ B, (∀ i, xs i c = 0) → c = 0) :
    Set.InjOn (colMap ((G : K) ^ 3) xs) (B : Set V) := by sorry
