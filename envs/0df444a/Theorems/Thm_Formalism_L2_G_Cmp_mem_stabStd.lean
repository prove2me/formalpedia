-- Prove2me | Theorems.Thm_Formalism_L2_G_Cmp_mem_stabStd
-- name    : Formalism.L2.G.Cmp.mem_stabStd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:12:14.921953+00:00
-- url     : https://prove2.me/theorems/92ec8d48-7510-4d9c-8aef-6049ad7889d0
-- title:
--   Cmp: mem stab Std
-- statement:
--   The Cmp construction uses the mem stab Std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsLat.lean#L113-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsLat.lean#L113-L113

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
variable (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k : ℕ}

theorem Formalism.L2.G.Cmp.mem_stabStd (g : GL (Fin k) Qq) : g ∈ stabStd (k := k) (Qq := Qq) W ↔ gMap W g (stdL W) = stdL W := by sorry
