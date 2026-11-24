-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_neg
-- name    : Formalism.MainNotions.PlaneGram.vala_neg
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:08:04.791974+00:00
-- url     : https://prove2.me/theorems/23620958-c0f1-4ebf-a1aa-6efbb34801ef
-- title:
--   Plane Gram: vala neg
-- statement:
--   The Plane Gram construction uses the vala neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L956-L959
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L956-L959

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

theorem Formalism.MainNotions.PlaneGram.vala_neg {θ : ℝ} {F : MvPolynomial (L × Fin r) K} (hF : vala sg S θ F) :
    vala sg S θ (-F) := by sorry
