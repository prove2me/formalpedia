-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_rowMap_injOn
-- name    : Formalism.BranchingDeterminantCap.PrismTransfer.rowMap_injOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:19:30.28723+00:00
-- url     : https://prove2.me/theorems/aff4f9fb-284e-43d6-b2c8-c31a57c5a927
-- title:
--   Prism Transfer: row Map inj On
-- statement:
--   The Prism Transfer construction uses the row Map inj On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L391-L400
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L391-L400

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

theorem Formalism.BranchingDeterminantCap.PrismTransfer.rowMap_injOn {n : ℕ} (G : ℕ) (hG : 0 < G) (x : Fin n → V →ₗ[K] V) (A : Submodule (𝓞 K) V)
    (h : ∀ a : Fin n → V, (∀ i, a i ∈ A) → ∑ i, x i (a i) = 0 → a = 0) :
    Set.InjOn (rowMap ((G : K) ^ 3) x) ((Submodule.pi Set.univ fun _ : Fin n => A : Submodule (𝓞 K) (Fin n → V)) : Set (Fin n → V)) := by sorry
