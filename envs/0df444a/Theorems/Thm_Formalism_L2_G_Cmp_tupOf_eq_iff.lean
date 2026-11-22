-- Prove2me | Theorems.Thm_Formalism_L2_G_Cmp_tupOf_eq_iff
-- name    : Formalism.L2.G.Cmp.tupOf_eq_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:47:25.134373+00:00
-- url     : https://prove2.me/theorems/3bcdf04f-1447-4adf-a0a2-ff569b7381e7
-- title:
--   Cmp: tup Of eq iff
-- statement:
--   The Cmp construction uses the tup Of eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsLat.lean#L155-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsLat.lean#L155-L163

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_ClsLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Cmp
open Formalism.MainNotions.G Matrix
variable (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k nV : ℕ}

theorem Formalism.L2.G.Cmp.tupOf_eq_iff (g h : Fin nV → GL (Fin k) Qq) :
    tupOf W g = tupOf W h ↔ h⁻¹ * g ∈ stabTup (nV := nV) (k := k) (Qq := Qq) W := by sorry
