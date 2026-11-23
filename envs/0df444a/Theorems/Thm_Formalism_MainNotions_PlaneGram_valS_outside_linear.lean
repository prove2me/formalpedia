-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_outside_linear
-- name    : Formalism.MainNotions.PlaneGram.valS_outside_linear
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:46:24.454729+00:00
-- url     : https://prove2.me/theorems/f5bf033a-81ea-4ec1-99df-519104a1ad36
-- title:
--   Plane Gram: val S outside linear
-- statement:
--   The Plane Gram construction uses the val S outside linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L512-L532
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L512-L532

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
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ}
  (out : L → Prop) [DecidablePred out]
variable (sg : L → Bool) (S : Finset L)

theorem Formalism.MainNotions.PlaneGram.valS_outside_linear (Φ : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K)
    (hout : ∀ i ∈ S, ¬ out i)
    (h1 : ∀ α, Φ (monomial α 1) = monomial (eIn out α) 1 * Φ (monomial (eOut out α) 1))
    (h2 : ∀ α, 0 ≤ valS sg S (Φ (monomial (eOut out α) 1))) (F : MvPolynomial (L × Fin r) K) :
    valS sg S F ≤ valS sg S (Φ F) := by sorry
