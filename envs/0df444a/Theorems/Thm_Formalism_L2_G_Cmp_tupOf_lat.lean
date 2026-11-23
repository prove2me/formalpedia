-- Prove2me | Theorems.Thm_Formalism_L2_G_Cmp_tupOf_lat
-- name    : Formalism.L2.G.Cmp.tupOf_lat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:37.508056+00:00
-- url     : https://prove2.me/theorems/fdf49302-e115-4df5-9030-1d0fce330e20
-- title:
--   Cmp: tup Of lat
-- statement:
--   The Cmp construction uses the tup Of lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsLat.lean#L169-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsLat.lean#L169-L169

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

theorem Formalism.L2.G.Cmp.tupOf_lat (g : Fin nV → GL (Fin k) Qq) (v : Fin nV) : IsLattice W (tupOf W g v) := by sorry
