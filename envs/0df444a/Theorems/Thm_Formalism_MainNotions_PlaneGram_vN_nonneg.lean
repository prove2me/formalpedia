-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vN_nonneg
-- name    : Formalism.MainNotions.PlaneGram.vN_nonneg
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:07:49.730541+00:00
-- url     : https://prove2.me/theorems/914f57e9-eb2b-4cb6-bb3b-c9e6e06bcdfd
-- title:
--   Plane Gram: v N nonneg
-- statement:
--   The Plane Gram construction uses the v N nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L259-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L259-L261

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

theorem Formalism.MainNotions.PlaneGram.vN_nonneg (hD : DVRHyp v p) (n : ℕ) : 0 ≤ vN v n := by sorry
