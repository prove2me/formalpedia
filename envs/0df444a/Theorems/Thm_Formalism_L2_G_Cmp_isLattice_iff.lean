-- Prove2me | Theorems.Thm_Formalism_L2_G_Cmp_isLattice_iff
-- name    : Formalism.L2.G.Cmp.isLattice_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:25.171584+00:00
-- url     : https://prove2.me/theorems/3dea64e2-2206-4723-859a-f98d29be77fd
-- title:
--   Cmp: is Lattice iff
-- statement:
--   The Cmp construction uses the is Lattice iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsLat.lean#L46-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsLat.lean#L46-L55

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

theorem Formalism.L2.G.Cmp.isLattice_iff (L : Submodule W (Fin k → Qq)) : IsLattice W L ↔ ∃ g : GL (Fin k) Qq, L = gMap W g (stdL W) := by sorry
