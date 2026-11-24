-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_LatticeIndexAlt_map_comap_sub
-- name    : Formalism.IncomingBounds.LatticeIndexAlt.map_comap_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:25.714668+00:00
-- url     : https://prove2.me/theorems/70f0b319-51b3-471b-b130-3698f799e02d
-- title:
--   Lattice Index Alt: map comap sub
-- statement:
--   The Lattice Index Alt construction uses the map comap sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/IndexLastReductionHolds.lean#L17-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/IndexLastReductionHolds.lean#L17-L26

import Definitions.Def_Formalism_IncomingBounds_IndexLastStep
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndexSigned
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_IndexLastReductionHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open scoped Pointwise
open Formalism Formalism.IncomingBounds Formalism.IncomingBounds.LatticeIndexAlt
open Formalism.LatticeIndexTer
variable {O K X : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X]
  [IsScalarTower O K X]

theorem Formalism.IncomingBounds.LatticeIndexAlt.map_comap_sub (W : Submodule K X) (A : Submodule O X) :
    (A.comap ((W.subtype).restrictScalars O)).map ((W.subtype).restrictScalars O) =
      A ⊓ W.restrictScalars O := by sorry
