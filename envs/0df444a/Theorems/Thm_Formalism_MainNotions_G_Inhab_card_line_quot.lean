-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_Inhab_card_line_quot
-- name    : Formalism.MainNotions.G.Inhab.card_line_quot
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T09:56:50.325798+00:00
-- url     : https://prove2.me/theorems/657db0e4-4f9c-4114-88c9-1d6f1d94c2e6
-- title:
--   Inhab: card line quot
-- statement:
--   The Inhab construction uses the card line quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataLPb.lean#L71-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataLPb.lean#L71-L75

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLPb
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

theorem Formalism.MainNotions.G.Inhab.card_line_quot (h : HidaSetting p n' W Qq O Kf ι σ j w) (a : ℤ) :
    Nat.card (↥(line W (Qq := Qq) p a) ⧸ Submodule.comap (line W (Qq := Qq) p a).subtype (line W p (a + 1))) =
      p ^ n' := by sorry
