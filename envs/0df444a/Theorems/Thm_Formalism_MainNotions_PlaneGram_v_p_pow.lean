-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_v_p_pow
-- name    : Formalism.MainNotions.PlaneGram.v_p_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:05:52.455038+00:00
-- url     : https://prove2.me/theorems/0a00767b-c8ec-4a12-9aa9-cdf25b1ad9bd
-- title:
--   Plane Gram: v p pow
-- statement:
--   The Plane Gram construction uses the v p pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L239-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L239-L240

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

theorem Formalism.MainNotions.PlaneGram.v_p_pow (hD : DVRHyp v p) (n : ℕ) : v ((p : K) ^ n) = ((n : ℚ) : WithTop ℚ) := by sorry
