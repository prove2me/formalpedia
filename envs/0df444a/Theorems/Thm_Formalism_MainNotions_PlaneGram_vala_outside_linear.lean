-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_outside_linear
-- name    : Formalism.MainNotions.PlaneGram.vala_outside_linear
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:07:37.351867+00:00
-- url     : https://prove2.me/theorems/5b53d513-8893-47a9-b10f-402631c93070
-- title:
--   Plane Gram: vala outside linear
-- statement:
--   The Plane Gram construction uses the vala outside linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1012-L1018
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1012-L1018

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

theorem Formalism.MainNotions.PlaneGram.vala_outside_linear {θ : ℝ}
    (Φ : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K)
    (out : L → Prop) [DecidablePred out] (hout : ∀ i ∈ S, ¬ out i)
    (h1 : ∀ α, Φ (monomial α 1) = monomial (eIn out α) 1 * Φ (monomial (eOut out α) 1))
    (h2 : ∀ α, 0 ≤ valS sg S (Φ (monomial (eOut out α) 1))) {F : MvPolynomial (L × Fin r) K}
    (hF : vala sg S θ F) : vala sg S θ (Φ F) := by sorry
