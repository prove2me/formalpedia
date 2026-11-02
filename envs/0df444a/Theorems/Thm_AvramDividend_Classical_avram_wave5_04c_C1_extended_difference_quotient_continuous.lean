-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_extended_difference_quotient_continuous
-- name    : AvramDividend.Classical.avram_wave5_04c_C1_extended_difference_quotient_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T18:10:23.441789+00:00
-- url     : https://prove2.me/theorems/31fbc7d3-d96e-458a-802e-a194df63910e
-- title:
--   C1 point derivative extends difference quotient continuously over a region
-- statement:
--   If the payoff-coordinate map is differentiable at the endpoint and continuous elsewhere on a region, its divided difference extends continuously when the missing endpoint is filled with the true derivative. Apply this to the C1 logarithmic pullback on a compact subinterval of (0,1] to establish the continuous weighted polynomial approximation input. Uses real derivative, no C2 assumption.
-- source:
--   Mathlib HasDerivAt.continuousAt_div and continuousAt_update_of_ne; no stochastic proxy.

import Mathlib
set_option autoImplicit false
open Filter Set

theorem AvramDividend.Classical.avram_wave5_04c_C1_extended_difference_quotient_continuous
    (f : ℝ → ℝ) (c a : ℝ)
    (hf : HasDerivAt f a c) (s : Set ℝ)
    (hfc : ∀ t ∈ s, t ≠ c → ContinuousAt f t) :
    ContinuousOn
      (Function.update (fun t : ℝ => (f t - f c) / (t - c)) c a) s := by sorry
