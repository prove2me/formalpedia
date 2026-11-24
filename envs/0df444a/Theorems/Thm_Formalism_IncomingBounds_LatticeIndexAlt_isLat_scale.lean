-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_LatticeIndexAlt_isLat_scale
-- name    : Formalism.IncomingBounds.LatticeIndexAlt.isLat_scale
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:14:00.859215+00:00
-- url     : https://prove2.me/theorems/e6c07146-cfac-4461-9ce7-01e7bbc6f1fd
-- title:
--   Lattice Index Alt: is Lat scale
-- statement:
--   The Lattice Index Alt construction uses the is Lat scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/IndexLastReductionHolds.lean#L61-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/IndexLastReductionHolds.lean#L61-L70

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
omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K]

theorem Formalism.IncomingBounds.LatticeIndexAlt.isLat_scale {Y : Type} [AddCommGroup Y] [Module K Y] [Module O Y] [IsScalarTower O K Y]
    (c : K) (hc : c ≠ 0) (A : Submodule O Y) (hA : IsLat O K Y A) :
    IsLat O K Y (A.map ((c • LinearMap.id : Y →ₗ[K] Y).restrictScalars O)) := by sorry
