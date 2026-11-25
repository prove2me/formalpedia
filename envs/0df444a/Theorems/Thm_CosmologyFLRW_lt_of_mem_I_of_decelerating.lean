-- Prove2me | Theorems.Thm_CosmologyFLRW_lt_of_mem_I_of_decelerating
-- name    : CosmologyFLRW.lt_of_mem_I_of_decelerating
-- status  : Open
-- author  : @LG
-- created : 2026-11-25T02:07:21.058621+00:00
-- url     : https://prove2.me/theorems/034dc434-f8b5-43f1-a2db-e278912b7e86
-- title:
--   Strict Big-Bang time bound under deceleration
-- statement:
--   Let U be a model from the accompanying definition whose scale factor has nonpositive second derivative throughout U.I. If t₀∈U.I and a′(t₀)>0, then every t∈U.I satisfies t₀−a(t₀)/a′(t₀)<t. The denominator is strictly positive by hypothesis.
-- source:
--   Joseph Tooby-Smith and Luis Gabriel C. Bariuan, Physlib, “The Friedmann–Lemaître–Robertson–Walker metric,” Physlib/Cosmology/FLRW/Basic.lean, commit 85bb8f5df598f6701be57a70f06e08069e30589c; https://github.com/leanprover-community/physlib/blob/85bb8f5df598f6701be57a70f06e08069e30589c/Physlib/Cosmology/FLRW/Basic.lean; lemma lt_of_mem_I_of_decelerating, lines 265–279.

import Definitions.Def_FLRWBigBangBound

namespace CosmologyFLRW

/-- Every time in the interval lies strictly after the extrapolated zero of the
scale factor's tangent at any expanding time, provided the model decelerates
throughout the interval. -/
theorem lt_of_mem_I_of_decelerating (U : FLRWModel)
    (hdec : ∀ s ∈ U.I, deriv (deriv U.a) s ≤ 0)
    {t₀ : ℝ} (ht₀ : t₀ ∈ U.I) (h0 : 0 < deriv U.a t₀)
    {t : ℝ} (ht : t ∈ U.I) :
    t₀ - U.a t₀ / deriv U.a t₀ < t := by
  sorry

end CosmologyFLRW
