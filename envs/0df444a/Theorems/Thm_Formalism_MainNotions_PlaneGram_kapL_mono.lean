-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_kapL_mono
-- name    : Formalism.MainNotions.PlaneGram.kapL_mono
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:07:13.703477+00:00
-- url     : https://prove2.me/theorems/086c06a8-e1f4-48bd-9b2d-638a02e2ec50
-- title:
--   Plane Gram: kap L mono
-- statement:
--   The Plane Gram construction uses the kap L mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L390-L402
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L390-L402

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

theorem Formalism.MainNotions.PlaneGram.kapL_mono {p : ℕ} (hp : 2 ≤ p) (r : ℕ) {L : Type} [Fintype L] {d d' : L → ℕ}
    (h : ∀ i, d i ≤ d' i) : kapL p r d ≤ kapL p r d' := by sorry
