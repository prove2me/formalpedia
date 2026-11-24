-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_Inhab_map_line
-- name    : Formalism.MainNotions.G.Inhab.map_line
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T09:55:59.537894+00:00
-- url     : https://prove2.me/theorems/e79d7c05-8e24-4777-9824-6fc8c69d5611
-- title:
--   Inhab: map line
-- statement:
--   The Inhab construction uses the map line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataLoc.lean#L115-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataLoc.lean#L115-L122

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatSetting
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.Inhab
open Formalism.MainNotions.G
variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem Formalism.MainNotions.G.Inhab.map_line (h : HidaSetting p n' W Qq O Kf ι σ j w) (a n : ℤ) :
    (line W (Qq := Qq) p n).map
      ((Matrix.mulVecLin (Matrix.scalar (Fin 1) ((p : Qq) ^ a))).restrictScalars W) = line W p (a + n) := by sorry
