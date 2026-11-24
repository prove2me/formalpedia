-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_coeff_substS
-- name    : Formalism.MainNotions.PlaneGram.coeff_substS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:59.514792+00:00
-- url     : https://prove2.me/theorems/4919cde9-9e90-4f9d-a65b-3a6d883668cb
-- title:
--   Plane Gram: coeff subst S
-- statement:
--   The Plane Gram construction uses the coeff subst S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L255-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L255-L259

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

theorem Formalism.MainNotions.PlaneGram.coeff_substS (F : MvPolynomial (L × Fin r) K) (β : L × Fin r →₀ ℕ) :
    (substS ι sg S A B F).coeff β =
      ∑ α ∈ F.support, ι (F.coeff α) * (substS ι sg S A B (monomial α 1)).coeff β := by sorry
