-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_mono
-- name    : Formalism.MainNotions.PlaneGram.vge_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:14:44.514456+00:00
-- url     : https://prove2.me/theorems/33d5b982-9d9e-499e-b0fe-70ebeaa5f0a8
-- title:
--   Plane Gram: vge mono
-- statement:
--   The Plane Gram construction uses the vge mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L21-L23

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

theorem Formalism.MainNotions.PlaneGram.vge_mono {a b : ℝ} {x : K} (h : b ≤ a) (hx : vge v a x) : vge v b x := by sorry
