-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_v_natCast
-- name    : Formalism.MainNotions.PlaneGram.v_natCast
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:05:39.790828+00:00
-- url     : https://prove2.me/theorems/5557ec93-d434-435c-8637-563f0e4bcb3c
-- title:
--   Plane Gram: v nat Cast
-- statement:
--   The Plane Gram construction uses the v nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L242-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L242-L251

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
variable {v} {p : ℕ} [CharZero K]

theorem Formalism.MainNotions.PlaneGram.v_natCast (hD : DVRHyp v p) {n : ℕ} (hn : n ≠ 0) :
    v (n : K) = ((padicValNat p n : ℚ) : WithTop ℚ) := by sorry
