-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_of_add_le
-- name    : Formalism.MainNotions.PlaneGram.vala_of_add_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:08:14.75032+00:00
-- url     : https://prove2.me/theorems/988d45e9-711c-4bb5-8df6-045f8cf74f3b
-- title:
--   Plane Gram: vala of add le
-- statement:
--   The Plane Gram construction uses the vala of add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1025-L1031
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1025-L1031

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

theorem Formalism.MainNotions.PlaneGram.vala_of_add_le {θ : ℝ} (k : ℤ) {F G : MvPolynomial (L × Fin r) K}
    (h : valS sg S F + ((k : ℤ) : WithTop ℤ) ≤ valS sg S G) (hF : vala sg S θ F) :
    vala sg S (θ + k) G := by sorry
