-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_mul
-- name    : Formalism.MainNotions.PlaneGram.cge_mul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:06:50.22281+00:00
-- url     : https://prove2.me/theorems/cc164a81-2abf-4324-a233-56bcfb8f9da4
-- title:
--   Plane Gram: cge mul
-- statement:
--   The Plane Gram construction uses the cge mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L157-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L157-L162

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

theorem Formalism.MainNotions.PlaneGram.cge_mul {σ : Type} {a b : ℝ} {F G : MvPolynomial σ K} (hF : cge v a F) (hG : cge v b G) :
    cge v (a + b) (F * G) := by sorry
