-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_LatticeIndexBis_core
-- name    : Formalism.LatticeBaseChangeAlt.LatticeIndexBis.core
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:20.203801+00:00
-- url     : https://prove2.me/theorems/5e63b726-67ef-44c2-817b-2bd765e8435e
-- title:
--   Lattice Index Bis: core
-- statement:
--   The Lattice Index Bis construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LatticeIndexBis.lean#L60-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LatticeIndexBis.lean#L60-L101

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_BetaSesquilinearity
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndexSigned
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LatticeIndexBis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module
open Formalism.LatticeBaseChangeAlt.LatticeIndexBis
variable {O K V ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
  [IsScalarTower O K V]

theorem Formalism.LatticeBaseChangeAlt.LatticeIndexBis.core [Fintype ι] [DecidableEq ι] (a b : ι → V) (ha : LinearIndependent K a)
    (hb : LinearIndependent K b)
    (hab : Submodule.span K (Set.range a) = Submodule.span K (Set.range b))
    (P : Matrix ι ι K) (hP : ∀ i, a i = ∑ k, P k i • b k) :
    P.det ≠ 0 ∧ ∀ x y : O, x ≠ 0 → y ≠ 0 → algebraMap O K x = P.det * algebraMap O K y →
      Formalism.LatticeIndexTer.idx O V (Submodule.span O (Set.range b)) (Submodule.span O (Set.range a)) =
        ((IsDiscreteValuationRing.addVal O x).toNat : ℤ) -
          ((IsDiscreteValuationRing.addVal O y).toNat : ℤ) := by sorry
