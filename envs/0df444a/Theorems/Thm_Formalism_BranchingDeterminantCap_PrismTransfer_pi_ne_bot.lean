-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_pi_ne_bot
-- name    : Formalism.BranchingDeterminantCap.PrismTransfer.pi_ne_bot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:19:11.056244+00:00
-- url     : https://prove2.me/theorems/a25c7d0a-cc64-4503-9a81-6cf6ad6a8bbb
-- title:
--   Prism Transfer: pi ne bot
-- statement:
--   The Prism Transfer construction uses the pi ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L354-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L354-L367

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

theorem Formalism.BranchingDeterminantCap.PrismTransfer.pi_ne_bot {n : ℕ} (hn : 0 < n) (A : Submodule (𝓞 K) V) (hA : A ≠ ⊥) :
    (Submodule.pi Set.univ fun _ : Fin n => A) ≠ ⊥ := by sorry
