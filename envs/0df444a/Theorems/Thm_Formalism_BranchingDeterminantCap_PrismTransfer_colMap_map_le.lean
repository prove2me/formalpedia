-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_colMap_map_le
-- name    : Formalism.BranchingDeterminantCap.PrismTransfer.colMap_map_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:21:17.107522+00:00
-- url     : https://prove2.me/theorems/2f6e8981-11dc-41b0-8182-f0b634feb256
-- title:
--   Prism Transfer: col Map map le
-- statement:
--   The Prism Transfer construction uses the col Map map le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L379-L389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L379-L389

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

theorem Formalism.BranchingDeterminantCap.PrismTransfer.colMap_map_le {n : ℕ} (G : ℕ) (xs : Fin n → V →ₗ[K] V) (A B : Submodule (𝓞 K) V)
    (h : ∀ i, ∀ c ∈ B, ((G : 𝓞 K) ^ 3) • xs i c ∈ A) :
    B.map ((colMap ((G : K) ^ 3) xs).restrictScalars (𝓞 K)) ≤
      Submodule.pi Set.univ fun _ : Fin n => A := by sorry
