-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_of_le
-- name    : Formalism.MainNotions.PlaneGram.vala_of_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T19:14:42.315202+00:00
-- url     : https://prove2.me/theorems/d65f54f3-8c67-4d22-a5c8-61b34d056c25
-- title:
--   Plane Gram: vala of le
-- statement:
--   The Plane Gram construction uses the vala of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L932-L935
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L932-L935

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

theorem Formalism.MainNotions.PlaneGram.vala_of_le {θ : ℝ} {L' : Type} [DecidableEq L'] {sg' : L' → Bool} {S' : Finset L'}
    {F : MvPolynomial (L × Fin r) K} {G : MvPolynomial (L' × Fin r) K}
    (h : valS sg S F ≤ valS sg' S' G) (hF : vala sg S θ F) : vala sg' S' θ G := by sorry
