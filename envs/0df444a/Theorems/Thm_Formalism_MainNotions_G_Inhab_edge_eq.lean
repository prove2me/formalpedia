-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_Inhab_edge_eq
-- name    : Formalism.MainNotions.G.Inhab.edge_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:44.920852+00:00
-- url     : https://prove2.me/theorems/2adad871-98ca-42fe-ae4a-10d0dbbab86e
-- title:
--   Inhab: edge eq
-- statement:
--   The Inhab construction uses the edge eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataLPb.lean#L84-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataLPb.lean#L84-L107

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

theorem Formalism.MainNotions.G.Inhab.edge_eq (h : HidaSetting p n' W Qq O Kf ι σ j w) (e : Edge W Qq 1) (he : IsEdge p n' 1 e) :
    ∃ a : ℤ, e = edge1 W Qq p a := by sorry
