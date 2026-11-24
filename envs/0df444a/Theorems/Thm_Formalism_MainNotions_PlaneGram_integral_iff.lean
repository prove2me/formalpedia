-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_integral_iff
-- name    : Formalism.MainNotions.PlaneGram.integral_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:07:02.084541+00:00
-- url     : https://prove2.me/theorems/50809c10-b66b-4be6-b30e-4431217dee1b
-- title:
--   Plane Gram: integral iff
-- statement:
--   The Plane Gram construction uses the integral iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsMonomialOrder.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsMonomialOrder.lean#L30-L31

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsMonomialOrder
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
variable {v}
variable {σ τ : Type}

theorem Formalism.MainNotions.PlaneGram.integral_iff (F : MvPolynomial σ K) : Integral v F ↔ 0 ≤ vG v F := by sorry
