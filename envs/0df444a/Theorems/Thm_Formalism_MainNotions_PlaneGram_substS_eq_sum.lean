-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_substS_eq_sum
-- name    : Formalism.MainNotions.PlaneGram.substS_eq_sum
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:08:16.402987+00:00
-- url     : https://prove2.me/theorems/33998933-1100-4f95-ae1a-7735df92bb48
-- title:
--   Plane Gram: subst S eq sum
-- statement:
--   The Plane Gram construction uses the subst S eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L249-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L249-L253

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

theorem Formalism.MainNotions.PlaneGram.substS_eq_sum (F : MvPolynomial (L × Fin r) K) :
    substS ι sg S A B F =
      ∑ α ∈ F.support, C (ι (F.coeff α)) * substS ι sg S A B (monomial α 1) := by sorry
