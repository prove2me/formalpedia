-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_substS_monomial_of_free
-- name    : Formalism.MainNotions.PlaneGram.substS_monomial_of_free
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:07:47.097976+00:00
-- url     : https://prove2.me/theorems/b2c93a06-b112-4583-b564-69a121e32345
-- title:
--   Plane Gram: subst S monomial of free
-- statement:
--   The Plane Gram construction uses the subst S monomial of free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L270-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L270-L276

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

theorem Formalism.MainNotions.PlaneGram.substS_monomial_of_free (α : L × Fin r →₀ ℕ) (c : K) (h : ∀ x ∈ α.support, x.1 ∉ S) :
    substS ι sg S A B (monomial α c) = monomial α (ι c) := by sorry
