-- Prove2me | Theorems.Thm_CosmologyFLRW_scaleFactor_le_tangent
-- name    : CosmologyFLRW.scaleFactor_le_tangent
-- status  : Proved
-- author  : @LG
-- created : 2026-11-25T02:03:34.059788+00:00
-- url     : https://prove2.me/theorems/c55c9a88-d88b-4e69-a894-18c6ec3f875c
-- title:
--   Scale factor lies below its tangent line under deceleration
-- statement:
--   Let U be a model from the accompanying definition, and suppose its scale factor has nonpositive second derivative at every time in U.I. For any t₀,t∈U.I, the scale factor satisfies a(t)≤a(t₀)+a′(t₀)(t−t₀). No positivity assumption on a′(t₀) is imposed for this estimate.
-- source:
--   Joseph Tooby-Smith and Luis Gabriel C. Bariuan, Physlib, “The Friedmann–Lemaître–Robertson–Walker metric,” Physlib/Cosmology/FLRW/Basic.lean, commit 85bb8f5df598f6701be57a70f06e08069e30589c; https://github.com/leanprover-community/physlib/blob/85bb8f5df598f6701be57a70f06e08069e30589c/Physlib/Cosmology/FLRW/Basic.lean; lemma scaleFactor_le_tangent, lines 217–263.

import Definitions.Def_FLRWBigBangBound

namespace CosmologyFLRW

/-- A nonpositive second derivative makes the scale factor lie below its tangent
line at every pair of times in the model interval. -/
theorem scaleFactor_le_tangent (U : FLRWModel)
    (hdec : ∀ s ∈ U.I, deriv (deriv U.a) s ≤ 0)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ U.I) (ht : t ∈ U.I) :
    U.a t ≤ U.a t₀ + deriv U.a t₀ * (t - t₀) := by
  sorry

end CosmologyFLRW
