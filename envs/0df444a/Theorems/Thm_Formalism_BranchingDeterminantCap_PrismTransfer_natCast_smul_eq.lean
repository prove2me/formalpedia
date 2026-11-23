-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_natCast_smul_eq
-- name    : Formalism.BranchingDeterminantCap.PrismTransfer.natCast_smul_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:19:17.916915+00:00
-- url     : https://prove2.me/theorems/dc1e745b-6744-4ea3-ad43-de07601adda3
-- title:
--   Prism Transfer: nat Cast smul eq
-- statement:
--   The Prism Transfer construction uses the nat Cast smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L24-L25

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
open Formalism.BranchingDeterminantCap.PrismTransfer
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]

theorem Formalism.BranchingDeterminantCap.PrismTransfer.natCast_smul_eq (n : ℕ) (x : V) : (n : 𝓞 K) • x = (n : K) • x := by sorry
