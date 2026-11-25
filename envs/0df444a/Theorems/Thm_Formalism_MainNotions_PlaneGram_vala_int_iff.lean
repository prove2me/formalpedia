-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_int_iff
-- name    : Formalism.MainNotions.PlaneGram.vala_int_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:51:06.52401+00:00
-- url     : https://prove2.me/theorems/34cbe813-a206-4f6a-af65-eedf4a23fa61
-- title:
--   Plane Gram: vala int iff
-- statement:
--   The Plane Gram construction uses the vala int iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L923-L925
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L923-L925

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

theorem Formalism.MainNotions.PlaneGram.vala_int_iff (n : ℤ) (F : MvPolynomial (L × Fin r) K) :
    vala sg S (n : ℝ) F ↔ F ∈ Aset sg S n := by sorry
