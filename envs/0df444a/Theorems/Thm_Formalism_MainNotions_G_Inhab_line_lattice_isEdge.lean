-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_Inhab_line_lattice_isEdge
-- name    : Formalism.MainNotions.G.Inhab.line_lattice_isEdge
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T09:55:42.063874+00:00
-- url     : https://prove2.me/theorems/a57cfce4-c616-47f9-99fd-967d659599e8
-- title:
--   Inhab: line lattice is Edge
-- statement:
--   The Inhab construction uses the line lattice is Edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataLPb.lean#L80-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataLPb.lean#L80-L82

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

theorem Formalism.MainNotions.G.Inhab.line_lattice_isEdge (h : HidaSetting p n' W Qq O Kf ι σ j w) (a : ℤ) : IsEdge p n' 1 (edge1 W Qq p a) := by sorry
