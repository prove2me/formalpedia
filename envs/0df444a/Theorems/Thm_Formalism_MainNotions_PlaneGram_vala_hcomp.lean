-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_hcomp
-- name    : Formalism.MainNotions.PlaneGram.vala_hcomp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:46:36.838792+00:00
-- url     : https://prove2.me/theorems/be847184-6998-4de3-aeed-6b188555c098
-- title:
--   Plane Gram: vala hcomp
-- statement:
--   The Plane Gram construction uses the vala hcomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1009-L1010
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1009-L1010

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

theorem Formalism.MainNotions.PlaneGram.vala_hcomp [Fintype L] {θ : ℝ} (d : L → ℕ) {F : MvPolynomial (L × Fin r) K}
    (hF : vala sg S θ F) : vala sg S θ (hcomp d F) := by sorry
