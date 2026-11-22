-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_zero_iff_Integral
-- name    : Formalism.MainNotions.PlaneGram.cge_zero_iff_Integral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:05:40.469676+00:00
-- url     : https://prove2.me/theorems/a7bdfd5d-97f2-4090-8052-e5eace175eb4
-- title:
--   Plane Gram: cge zero iff Integral
-- statement:
--   The Plane Gram construction uses the cge zero iff Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L133-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L133-L133

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

theorem Formalism.MainNotions.PlaneGram.cge_zero_iff_Integral {σ : Type} (F : MvPolynomial σ K) : cge v 0 F ↔ Integral v F := by sorry
