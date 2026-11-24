-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_logb_add_mono
-- name    : Formalism.MainNotions.PlaneGram.logb_add_mono
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:07:29.488928+00:00
-- url     : https://prove2.me/theorems/a03a9e6d-f4a6-46b4-8e36-d86d36818dc5
-- title:
--   Plane Gram: logb add mono
-- statement:
--   The Plane Gram construction uses the logb add mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L372-L379
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L372-L379

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

theorem Formalism.MainNotions.PlaneGram.logb_add_mono {p : ℕ} (hp : 2 ≤ p) (r : ℕ) {a b : ℕ} (h : 1 ≤ a + r) (hab : a ≤ b) :
    Real.logb p ((a : ℝ) + r) ≤ Real.logb p ((b : ℝ) + r) := by sorry
