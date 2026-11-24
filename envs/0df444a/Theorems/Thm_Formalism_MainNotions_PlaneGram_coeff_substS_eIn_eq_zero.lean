-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_coeff_substS_eIn_eq_zero
-- name    : Formalism.MainNotions.PlaneGram.coeff_substS_eIn_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:08.411741+00:00
-- url     : https://prove2.me/theorems/5fbb1d50-5abd-488c-ae12-28319fc49f3e
-- title:
--   Plane Gram: coeff subst S e In eq zero
-- statement:
--   The Plane Gram construction uses the coeff subst S e In eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L294-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L294-L319

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

theorem Formalism.MainNotions.PlaneGram.coeff_substS_eIn_eq_zero (α δ : L × Fin r →₀ ℕ) (hδ : eOut out δ ≠ 0) :
    (substS ι sg S A B (monomial (eIn out α) 1)).coeff δ = 0 := by sorry
