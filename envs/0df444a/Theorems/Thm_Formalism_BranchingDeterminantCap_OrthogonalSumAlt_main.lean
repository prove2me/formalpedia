-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_main
-- name    : Formalism.BranchingDeterminantCap.OrthogonalSumAlt.main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:54.767656+00:00
-- url     : https://prove2.me/theorems/76aede74-8067-412e-954c-ad1da1177a4c
-- title:
--   Orthogonal Sum Alt: main
-- statement:
--   The Orthogonal Sum Alt construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/OrthSum.lean#L67-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/OrthSum.lean#L67-L120

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_OrthSum
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
open Formalism.BranchingDeterminantCap.OrthogonalSumAlt
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]

theorem Formalism.BranchingDeterminantCap.OrthogonalSumAlt.main (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {S : Type} (A : S → Submodule (𝓞 K) V) (hA : ∀ s, (A s).FG)
    (horth : ∀ s t, s ≠ t → OrthAt b X (A s) (A t)) (s : Finset S) :
    (⨆ i ∈ s, A i).FG ∧ Formalism.HN.rkK (⨆ i ∈ s, A i) = ∑ i ∈ s, Formalism.HN.rkK (A i) ∧
      Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize b X) (⨆ i ∈ s, A i) =
        ∑ i ∈ s, Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize b X) (A i) ∧
      ∀ c : ℝ, (∀ i ∈ s, A i ≠ ⊥ → Formalism.HN.muMax (Formalism.HermitianLatticesTheory.realize b X) (A i) ≤ c) →
        (⨆ i ∈ s, A i) ≠ ⊥ → Formalism.HN.muMax (Formalism.HermitianLatticesTheory.realize b X) (⨆ i ∈ s, A i) ≤ c := by sorry
