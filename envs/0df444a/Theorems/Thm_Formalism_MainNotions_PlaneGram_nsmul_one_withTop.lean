-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_nsmul_one_withTop
-- name    : Formalism.MainNotions.PlaneGram.nsmul_one_withTop
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:07:05.585846+00:00
-- url     : https://prove2.me/theorems/5ab13aae-d7f5-42a3-9f8b-95e6a000dc61
-- title:
--   Plane Gram: nsmul one with Top
-- statement:
--   The Plane Gram construction uses the nsmul one with Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L180-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L180-L185

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

theorem Formalism.MainNotions.PlaneGram.nsmul_one_withTop (e : ℕ) : e • (1 : WithTop ℚ) = ((e : ℚ) : WithTop ℚ) := by sorry
