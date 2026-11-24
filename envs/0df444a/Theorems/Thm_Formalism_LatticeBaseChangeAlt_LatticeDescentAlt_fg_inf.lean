-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_LatticeDescentAlt_fg_inf
-- name    : Formalism.LatticeBaseChangeAlt.LatticeDescentAlt.fg_inf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:17.176051+00:00
-- url     : https://prove2.me/theorems/8e6bd42c-df88-4dae-843d-589b0f02a602
-- title:
--   Lattice Descent Alt: fg inf
-- statement:
--   The Lattice Descent Alt construction uses the fg inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LatticeDescent.lean#L36-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LatticeDescent.lean#L36-L41

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_BetaSesquilinearity
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LatticeDescent
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
open Formalism.LatticeBaseChangeAlt.LatticeDescentAlt
variable {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

theorem Formalism.LatticeBaseChangeAlt.LatticeDescentAlt.fg_inf (M : Submodule O V) (hM : Formalism.LatticeIndexTer.IsLat O K V M) (N : Submodule O V) :
    (M ⊓ N).FG := by sorry
