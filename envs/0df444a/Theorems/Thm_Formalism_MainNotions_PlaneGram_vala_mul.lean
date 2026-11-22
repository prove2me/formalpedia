-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_mul
-- name    : Formalism.MainNotions.PlaneGram.vala_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:26.412999+00:00
-- url     : https://prove2.me/theorems/332adc54-b35f-4ea5-88f8-42697fe68ecf
-- title:
--   Plane Gram: vala mul
-- statement:
--   The Plane Gram construction uses the vala mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L965-L970
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L965-L970

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L)
variable {sg S}

theorem Formalism.MainNotions.PlaneGram.vala_mul {θ₁ θ₂ : ℝ} {F G : MvPolynomial (L × Fin r) K} (hF : vala sg S θ₁ F)
    (hG : vala sg S θ₂ G) : vala sg S (θ₁ + θ₂) (F * G) := by sorry
