-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_ms_htQ_bot
-- name    : Formalism.BranchingDeterminantCap.ms_htQ_bot
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:26:54.057809+00:00
-- url     : https://prove2.me/theorems/a03af697-43b7-468a-a368-98de8a659192
-- title:
--   Branching Determinant Cap: ms ht Q bot
-- statement:
--   The Branching Determinant Cap construction uses the ms ht Q bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/MapScale.lean#L36-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/MapScale.lean#L36-L65

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.HN
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]

theorem Formalism.BranchingDeterminantCap.ms_htQ_bot (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (A : Submodule (𝓞 K) V) : htQ b X A ⊥ = ht b X A := by sorry
