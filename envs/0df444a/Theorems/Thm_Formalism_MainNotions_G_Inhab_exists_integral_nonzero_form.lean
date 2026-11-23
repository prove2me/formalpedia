-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_Inhab_exists_integral_nonzero_form
-- name    : Formalism.MainNotions.G.Inhab.exists_integral_nonzero_form
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:40:43.344737+00:00
-- url     : https://prove2.me/theorems/43e748c0-34d3-4f33-a34b-ebfae1c785b9
-- title:
--   Inhab: exists integral nonzero form
-- statement:
--   The Inhab construction uses the exists integral nonzero form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataForm.lean#L184-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataForm.lean#L184-L211

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataForm
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
open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial
variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem Formalism.MainNotions.G.Inhab.exists_integral_nonzero_form (h : HidaSetting p n' W Qq O Kf ι σ j w) :
    ∃ F : (gat1 h).Fn, F ∈ (gat1 h).M ∧ F ∈ (gat1 h).Mna ∧ F ≠ 0 := by sorry
