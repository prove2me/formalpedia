-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_substS_mem
-- name    : Formalism.MainNotions.PlaneGram.substS_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:46.234882+00:00
-- url     : https://prove2.me/theorems/58eb06d5-db84-4a62-80a5-0eee6154c1b0
-- title:
--   Plane Gram: subst S mem
-- statement:
--   The Plane Gram construction uses the subst S mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L261-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L261-L268

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
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ} {R : Type} [CommRing R]
  (ι : K →+* R) (sg : L → Bool) (S : Finset L) (A B : Matrix (Fin r) (Fin r) R)

theorem Formalism.MainNotions.PlaneGram.substS_mem (T : Subring (MvPolynomial (L × Fin r) R)) (hC : ∀ c : K, C (ι c) ∈ T)
    (F : MvPolynomial (L × Fin r) K)
    (h : ∀ α ∈ F.support, ∀ x ∈ α.support, subX sg S A B x ∈ T) : substS ι sg S A B F ∈ T := by sorry
