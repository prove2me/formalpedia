-- Prove2me | Theorems.Thm_Formalism_L2_G_Cmp_stabStd_iff
-- name    : Formalism.L2.G.Cmp.stabStd_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:03:46.713802+00:00
-- url     : https://prove2.me/theorems/36020dfc-7c1a-4372-85e1-f388455b1663
-- title:
--   Cmp: stab Std iff
-- statement:
--   The Cmp construction uses the stab Std iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsLat.lean#L115-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsLat.lean#L115-L129

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

theorem Formalism.L2.G.Cmp.stabStd_iff (g : GL (Fin k) Qq) : g ∈ stabStd (k := k) (Qq := Qq) W ↔
    (∀ a b, (g : Matrix (Fin k) (Fin k) Qq) a b ∈ (algebraMap W Qq).range) ∧
      ∀ a b, ((g⁻¹ : GL (Fin k) Qq) : Matrix (Fin k) (Fin k) Qq) a b ∈ (algebraMap W Qq).range := by sorry
