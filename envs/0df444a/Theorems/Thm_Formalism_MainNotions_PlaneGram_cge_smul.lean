-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_smul
-- name    : Formalism.MainNotions.PlaneGram.cge_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:37:45.327805+00:00
-- url     : https://prove2.me/theorems/3e89c3c8-5a16-4c2a-babe-9c9c2aece7de
-- title:
--   Plane Gram: cge smul
-- statement:
--   The Plane Gram construction uses the cge smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L118-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L118-L122

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

theorem Formalism.MainNotions.PlaneGram.cge_smul {σ : Type} {a b : ℝ} {c : K} {F : MvPolynomial σ K} (hc : vge v a c)
    (hF : cge v b F) : cge v (a + b) (c • F) := by sorry
