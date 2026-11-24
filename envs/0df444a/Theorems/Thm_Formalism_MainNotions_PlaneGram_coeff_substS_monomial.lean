-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_coeff_substS_monomial
-- name    : Formalism.MainNotions.PlaneGram.coeff_substS_monomial
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:06:28.628423+00:00
-- url     : https://prove2.me/theorems/33237118-521a-452f-bdd2-9989e79e0f95
-- title:
--   Plane Gram: coeff subst S monomial
-- statement:
--   The Plane Gram construction uses the coeff subst S monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L332-L351
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L332-L351

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
variable (out : L → Prop) [DecidablePred out]

theorem Formalism.MainNotions.PlaneGram.coeff_substS_monomial (hout : ∀ i ∈ S, ¬ out i) (α γ : L × Fin r →₀ ℕ) :
    (substS ι sg S A B (monomial α 1)).coeff γ =
      if eOut out γ = eOut out α then (substS ι sg S A B (monomial (eIn out α) 1)).coeff (eIn out γ)
      else 0 := by sorry
