-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_mul_left_nonneg
-- name    : Formalism.MainNotions.PlaneGram.vala_mul_left_nonneg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T19:26:39.855618+00:00
-- url     : https://prove2.me/theorems/854fce51-a669-4113-ae80-ddfd81a51784
-- title:
--   Plane Gram: vala mul left nonneg
-- statement:
--   The Plane Gram construction uses the vala mul left nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L990-L993
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L990-L993

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

theorem Formalism.MainNotions.PlaneGram.vala_mul_left_nonneg {θ : ℝ} {F G : MvPolynomial (L × Fin r) K} (hF : 0 ≤ valS sg S F)
    (hG : vala sg S θ G) : vala sg S θ (F * G) := by sorry
