-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_Inhab_homoth_val
-- name    : Formalism.MainNotions.G.Inhab.homoth_val
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T09:55:46.936662+00:00
-- url     : https://prove2.me/theorems/0746e775-d2b1-45ad-9580-1573efca852a
-- title:
--   Inhab: homoth val
-- statement:
--   The Inhab construction uses the homoth val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataLoc.lean#L143-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataLoc.lean#L143-L147

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

theorem Formalism.MainNotions.G.Inhab.homoth_val (h : HidaSetting p n' W Qq O Kf ι σ j w) (γ : Multiplicative ℤ) :
    ((homoth h γ : GL (Fin 1) Qq) : Matrix (Fin 1) (Fin 1) Qq) =
      Matrix.scalar (Fin 1) ((p : Qq) ^ (Multiplicative.toAdd γ)) := by sorry
