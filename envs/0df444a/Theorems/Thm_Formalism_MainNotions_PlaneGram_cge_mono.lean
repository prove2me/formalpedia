-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_mono
-- name    : Formalism.MainNotions.PlaneGram.cge_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:45.353218+00:00
-- url     : https://prove2.me/theorems/338d4ab4-4700-46cd-ba54-2cecc191cf97
-- title:
--   Plane Gram: cge mono
-- statement:
--   The Plane Gram construction uses the cge mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L103-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L103-L104

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

theorem Formalism.MainNotions.PlaneGram.cge_mono {σ : Type} {a b : ℝ} {F : MvPolynomial σ K} (h : b ≤ a) (hF : cge v a F) :
    cge v b F := by sorry
