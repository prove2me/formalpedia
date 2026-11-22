-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_mono
-- name    : Formalism.MainNotions.PlaneGram.vala_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:17:12.7805+00:00
-- url     : https://prove2.me/theorems/9e10309d-acbc-422d-8a06-5d060ffd5420
-- title:
--   Plane Gram: vala mono
-- statement:
--   The Plane Gram construction uses the vala mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L929-L930
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L929-L930

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

theorem Formalism.MainNotions.PlaneGram.vala_mono {θ θ' : ℝ} (h : θ' ≤ θ) {F : MvPolynomial (L × Fin r) K} (hF : vala sg S θ F) :
    vala sg S θ' F := by sorry
