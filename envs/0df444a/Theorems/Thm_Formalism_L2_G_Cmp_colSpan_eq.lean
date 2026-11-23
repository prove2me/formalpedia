-- Prove2me | Theorems.Thm_Formalism_L2_G_Cmp_colSpan_eq
-- name    : Formalism.L2.G.Cmp.colSpan_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:15.849919+00:00
-- url     : https://prove2.me/theorems/b245de0a-487a-40d0-831a-f18adf719f92
-- title:
--   Cmp: col Span eq
-- statement:
--   The Cmp construction uses the col Span eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsLat.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsLat.lean#L39-L44

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

theorem Formalism.L2.G.Cmp.colSpan_eq (g : GL (Fin k) Qq) : colSpan W (g : Matrix (Fin k) (Fin k) Qq) = gMap W g (stdL W) := by sorry
