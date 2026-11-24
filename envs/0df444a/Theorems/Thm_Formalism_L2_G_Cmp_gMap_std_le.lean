-- Prove2me | Theorems.Thm_Formalism_L2_G_Cmp_gMap_std_le
-- name    : Formalism.L2.G.Cmp.gMap_std_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:32.079244+00:00
-- url     : https://prove2.me/theorems/53b4d0a6-8889-40d7-91aa-4a0e0268a7a1
-- title:
--   Cmp: g Map std le
-- statement:
--   The Cmp construction uses the g Map std le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsLat.lean#L87-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsLat.lean#L87-L96

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_ClsLat
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

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

theorem Formalism.L2.G.Cmp.gMap_std_le (g : GL (Fin k) Qq) :
    gMap W g (stdL W) ≤ stdL W ↔ ∀ a b, (g : Matrix (Fin k) (Fin k) Qq) a b ∈ (algebraMap W Qq).range := by sorry
