-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_LatticeIndexAlt_isLat_sup
-- name    : Formalism.IncomingBounds.LatticeIndexAlt.isLat_sup
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:04.231356+00:00
-- url     : https://prove2.me/theorems/40cd4ae2-45ca-4246-82b7-f93c9843693b
-- title:
--   Lattice Index Alt: is Lat sup
-- statement:
--   The Lattice Index Alt construction uses the is Lat sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/IndexLastReductionHolds.lean#L73-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/IndexLastReductionHolds.lean#L73-L78

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

theorem Formalism.IncomingBounds.LatticeIndexAlt.isLat_sup {Y : Type} [AddCommGroup Y] [Module K Y] [Module O Y] [IsScalarTower O K Y]
    (A B : Submodule O Y) (hA : A.FG) (hB : IsLat O K Y B) : IsLat O K Y (A ⊔ B) := by sorry
