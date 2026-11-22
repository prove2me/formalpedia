-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_sum
-- name    : Formalism.MainNotions.PlaneGram.vala_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:26.314552+00:00
-- url     : https://prove2.me/theorems/e17abda9-297c-4ab1-874d-c38fb36948d2
-- title:
--   Plane Gram: vala sum
-- statement:
--   The Plane Gram construction uses the vala sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L945-L948
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L945-L948

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

theorem Formalism.MainNotions.PlaneGram.vala_sum {θ : ℝ} {ι : Type} (s : Finset ι) (f : ι → MvPolynomial (L × Fin r) K)
    (h : ∀ i ∈ s, vala sg S θ (f i)) : vala sg S θ (∑ i ∈ s, f i) := by sorry
