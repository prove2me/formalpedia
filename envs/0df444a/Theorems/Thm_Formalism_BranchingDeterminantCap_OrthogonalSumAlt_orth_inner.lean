-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_orth_inner
-- name    : Formalism.BranchingDeterminantCap.OrthogonalSumAlt.orth_inner
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:19:05.636225+00:00
-- url     : https://prove2.me/theorems/52d5e5b6-1df0-4ce0-a229-ee12dd9e8dc0
-- title:
--   Orthogonal Sum Alt: orth inner
-- statement:
--   The Orthogonal Sum Alt construction uses the orth inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/OrthSum.lean#L60-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/OrthSum.lean#L60-L65

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

theorem Formalism.BranchingDeterminantCap.OrthogonalSumAlt.orth_inner (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    {A B : Submodule (𝓞 K) V} (h : OrthAt b X A B) :
    ∀ x ∈ A, ∀ y ∈ B, inner ℝ (Formalism.HermitianLatticesTheory.realize b X x) (Formalism.HermitianLatticesTheory.realize b X y) = 0 := by sorry
