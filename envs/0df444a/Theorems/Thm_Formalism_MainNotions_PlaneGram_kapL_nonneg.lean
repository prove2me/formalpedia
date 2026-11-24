-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_kapL_nonneg
-- name    : Formalism.MainNotions.PlaneGram.kapL_nonneg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:07:11.204682+00:00
-- url     : https://prove2.me/theorems/f10da260-54b5-4de2-a474-2601a9f237ef
-- title:
--   Plane Gram: kap L nonneg
-- statement:
--   The Plane Gram construction uses the kap L nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L387-L388
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L387-L388

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

theorem Formalism.MainNotions.PlaneGram.kapL_nonneg {p : ℕ} (hp : 2 ≤ p) (r : ℕ) {L : Type} [Fintype L] (d : L → ℕ) :
    0 ≤ kapL p r d := by sorry
