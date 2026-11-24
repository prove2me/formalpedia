-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_LatticeIndexAlt_idx_comap
-- name    : Formalism.IncomingBounds.LatticeIndexAlt.idx_comap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:12.241823+00:00
-- url     : https://prove2.me/theorems/693bdc65-29d2-4353-a271-3240b4709548
-- title:
--   Lattice Index Alt: idx comap
-- statement:
--   The Lattice Index Alt construction uses the idx comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/IndexLastReductionHolds.lean#L53-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/IndexLastReductionHolds.lean#L53-L57

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

theorem Formalism.IncomingBounds.LatticeIndexAlt.idx_comap (W : Submodule K X) (A B : Submodule O X) :
    idx O W (A.comap ((W.subtype).restrictScalars O)) (B.comap ((W.subtype).restrictScalars O)) =
      idx O X (A ⊓ W.restrictScalars O) (B ⊓ W.restrictScalars O) := by sorry
