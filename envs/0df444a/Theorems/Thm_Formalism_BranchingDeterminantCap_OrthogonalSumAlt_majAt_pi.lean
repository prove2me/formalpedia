-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_majAt_pi
-- name    : Formalism.BranchingDeterminantCap.OrthogonalSumAlt.majAt_pi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:18:56.697846+00:00
-- url     : https://prove2.me/theorems/78d1321f-d924-4e30-93e6-8df5c6b4e004
-- title:
--   Orthogonal Sum Alt: maj At pi
-- statement:
--   The Orthogonal Sum Alt construction uses the maj At pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/OrthSum.lean#L175-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/OrthSum.lean#L175-L180

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

theorem Formalism.BranchingDeterminantCap.OrthogonalSumAlt.majAt_pi (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (n : ℕ) (v : InfinitePlace K) (x y : Fin n → V) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basis fun _ : Fin n => b)
      (fun v => Matrix.blockDiagonal' fun _ : Fin n => X v) v x y =
        ∑ j, Formalism.HermitianLatticesTheory.majAt b X v (x j) (y j) := by sorry
