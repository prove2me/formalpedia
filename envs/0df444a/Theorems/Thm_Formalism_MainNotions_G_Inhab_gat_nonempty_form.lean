-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_Inhab_gat_nonempty_form
-- name    : Formalism.MainNotions.G.Inhab.gat_nonempty_form
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:52:00.162784+00:00
-- url     : https://prove2.me/theorems/8d1379ed-23fb-4e09-93c2-8c69308b3794
-- title:
--   Inhab: gat nonempty form
-- statement:
--   The Inhab construction uses the gat nonempty form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataForm.lean#L213-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataForm.lean#L213-L220

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

theorem Formalism.MainNotions.G.Inhab.gat_nonempty_form (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    ∃ G : GAtP p, 1 ≤ G.P.nV ∧ G.TrivStab ∧ G.FinClasses ∧ G.M ≠ ⊥ ∧ G.Mna ≠ ⊥ := by sorry
