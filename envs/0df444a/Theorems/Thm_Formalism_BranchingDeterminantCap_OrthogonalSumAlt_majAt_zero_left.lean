-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_majAt_zero_left
-- name    : Formalism.BranchingDeterminantCap.OrthogonalSumAlt.majAt_zero_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:18:51.374063+00:00
-- url     : https://prove2.me/theorems/385d2686-3194-4d87-993e-84f31ac9d38c
-- title:
--   Orthogonal Sum Alt: maj At zero left
-- statement:
--   The Orthogonal Sum Alt construction uses the maj At zero left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/OrthSum.lean#L182-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/OrthSum.lean#L182-L184

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

theorem Formalism.BranchingDeterminantCap.OrthogonalSumAlt.majAt_zero_left (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (y : V) : Formalism.HermitianLatticesTheory.majAt b X v 0 y = 0 := by sorry
