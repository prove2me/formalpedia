-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_C_mul
-- name    : Formalism.MainNotions.PlaneGram.vala_C_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:51:15.967319+00:00
-- url     : https://prove2.me/theorems/1d79f471-422a-45d2-924c-56e3f67863e0
-- title:
--   Plane Gram: vala C mul
-- statement:
--   The Plane Gram construction uses the vala C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L953-L954
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L953-L954

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

theorem Formalism.MainNotions.PlaneGram.vala_C_mul {θ : ℝ} (a : K) {F : MvPolynomial (L × Fin r) K} (hF : vala sg S θ F) :
    vala sg S θ (C a * F) := by sorry
