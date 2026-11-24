-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_bin
-- name    : Formalism.MainNotions.PlaneGram.vge_bin
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:08:00.797912+00:00
-- url     : https://prove2.me/theorems/437c8b64-a9cf-416e-a995-d7282c8d600e
-- title:
--   Plane Gram: vge bin
-- statement:
--   The Plane Gram construction uses the vge bin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L44-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L44-L48

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
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
variable {K : Type} [Field K]
variable {σ : Type} [Fintype σ]

theorem Formalism.MainNotions.PlaneGram.vge_bin (v : AddValuation K (WithTop ℚ)) (M α : σ →₀ ℕ) : vge v 0 (bin M α : K) := by sorry
