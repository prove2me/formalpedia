-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_LatticeDescentAlt_span_inf_eq
-- name    : Formalism.LatticeBaseChangeAlt.LatticeDescentAlt.span_inf_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:17.959189+00:00
-- url     : https://prove2.me/theorems/e1c5e152-ee5c-4297-9f52-32096ce69367
-- title:
--   Lattice Descent Alt: span inf eq
-- statement:
--   The Lattice Descent Alt construction uses the span inf eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LatticeDescent.lean#L15-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LatticeDescent.lean#L15-L34

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

theorem Formalism.LatticeBaseChangeAlt.LatticeDescentAlt.span_inf_eq (M : Submodule O V) (hM : Formalism.LatticeIndexTer.IsLat O K V M) (V' : Submodule K V) :
    Submodule.span K ((M ⊓ V'.restrictScalars O : Submodule O V) : Set V) = V' := by sorry
