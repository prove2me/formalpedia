-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vN_multinomial_le
-- name    : Formalism.MainNotions.PlaneGram.vN_multinomial_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:08:18.250729+00:00
-- url     : https://prove2.me/theorems/7acf0c2b-ac8d-48e3-a912-586fefdac833
-- title:
--   Plane Gram: v N multinomial le
-- statement:
--   The Plane Gram construction uses the v N multinomial le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L462-L467
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L462-L467

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
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
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
variable {v} {p : ℕ} [CharZero K]

theorem Formalism.MainNotions.PlaneGram.vN_multinomial_le (hD : DVRHyp v p) {r : ℕ} (f : Fin r → ℕ) :
    vN v (Nat.multinomial univ f) ≤ (r : ℝ) * (Nat.log p (∑ a, f a) : ℝ) := by sorry
