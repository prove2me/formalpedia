-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_iff_Aset
-- name    : Formalism.MainNotions.PlaneGram.vala_iff_Aset
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:19.158857+00:00
-- url     : https://prove2.me/theorems/4fcbfb0c-cd66-4110-8449-9280a2948cab
-- title:
--   Plane Gram: vala iff Aset
-- statement:
--   The Plane Gram construction uses the vala iff Aset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L920-L921
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L920-L921

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

theorem Formalism.MainNotions.PlaneGram.vala_iff_Aset (θ : ℝ) (F : MvPolynomial (L × Fin r) K) :
    vala sg S θ F ↔ F ∈ Aset sg S ⌈θ⌉ := by sorry
