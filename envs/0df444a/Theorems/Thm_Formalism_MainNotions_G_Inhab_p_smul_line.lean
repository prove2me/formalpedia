-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_Inhab_p_smul_line
-- name    : Formalism.MainNotions.G.Inhab.p_smul_line
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T09:55:32.02485+00:00
-- url     : https://prove2.me/theorems/86bd185c-12ed-467d-82bc-04f7588fff57
-- title:
--   Inhab: p smul line
-- statement:
--   The Inhab construction uses the p smul line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataLPb.lean#L30-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataLPb.lean#L30-L37

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

theorem Formalism.MainNotions.G.Inhab.p_smul_line (h : HidaSetting p n' W Qq O Kf ι σ j w) (a : ℤ) (x : Fin 1 → Qq) (hx : x ∈ line W (Qq := Qq) p a) :
    (p : W) • x ∈ line W (Qq := Qq) p (a + 1) := by sorry
