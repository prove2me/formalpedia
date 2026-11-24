-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_v_natCast_of_not_dvd
-- name    : Formalism.MainNotions.PlaneGram.v_natCast_of_not_dvd
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:07:54.351805+00:00
-- url     : https://prove2.me/theorems/a05aaeaf-eed5-47d5-972c-14b78ac5fb00
-- title:
--   Plane Gram: v nat Cast of not dvd
-- statement:
--   The Plane Gram construction uses the v nat Cast of not dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L218-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L218-L237

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

theorem Formalism.MainNotions.PlaneGram.v_natCast_of_not_dvd (hD : DVRHyp v p) {m : ℕ} (h : ¬ p ∣ m) : v (m : K) = 0 := by sorry
