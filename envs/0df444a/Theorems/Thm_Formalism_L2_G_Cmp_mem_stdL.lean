-- Prove2me | Theorems.Thm_Formalism_L2_G_Cmp_mem_stdL
-- name    : Formalism.L2.G.Cmp.mem_stdL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:14.524202+00:00
-- url     : https://prove2.me/theorems/8cf30418-653d-44fb-beb0-83bdcdc5a91c
-- title:
--   Cmp: mem std L
-- statement:
--   The Cmp construction uses the mem std L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsLat.lean#L57-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsLat.lean#L57-L85

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

theorem Formalism.L2.G.Cmp.mem_stdL (x : Fin k → Qq) : x ∈ stdL (k := k) (Qq := Qq) W ↔ ∀ a, x a ∈ (algebraMap W Qq).range := by sorry
