-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_LatticeIndexBis_exists_indep
-- name    : Formalism.LatticeBaseChangeAlt.LatticeIndexBis.exists_indep
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T09:52:18.978222+00:00
-- url     : https://prove2.me/theorems/91b1f470-8753-40ea-afd4-d3a982e6dc09
-- title:
--   Lattice Index Bis: exists indep
-- statement:
--   The Lattice Index Bis construction uses the exists indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LatticeIndexBis.lean#L103-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LatticeIndexBis.lean#L103-L146

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

theorem Formalism.LatticeBaseChangeAlt.LatticeIndexBis.exists_indep [FiniteDimensional K V] (A : Submodule O V) (hA : A.FG) (U : Submodule K V)
    (hU : Submodule.span K (A : Set V) = U) :
    ∃ a : Fin (finrank K U) → V, LinearIndependent K a ∧ A = Submodule.span O (Set.range a) ∧
      Submodule.span K (Set.range a) = U := by sorry
