-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_positive_jump_tail_transform
-- name    : AvramDividend.Classical.discounted_positive_jump_tail_transform
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T21:18:37.806259+00:00
-- url     : https://prove2.me/theorems/c11235d7-6bc7-473b-91ce-07b3b4b0f546
-- title:
--   Discounted Lévy-tail Laplace transform as an integrated jump compensator
-- statement:
--   For any measure on nonnegative jump magnitudes and any θ>0, the exponentially discounted integral of the jump-tail mass equals the integral against the jump measure of (1-exp(-θz))/θ. This directly composes the weighted layer-cake identity and exponential integral already published in this mission, and is the exact analytic ingredient required for the bounded-variation Lévy–Khintchine/resolvent rewrite.
-- source:
--   Pinned Mathlib layer-cake and FTC, applied to the bounded-variation scale-function renewal transform of the Avram dividend mission

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Exponential transform of the positive-jump tail measure, combining the
weighted layer-cake identity with the exponential interval integral. -/
theorem discounted_positive_jump_tail_transform (μ : Measure ℝ≥0) (θ : ℝ) (hθ : 0 < θ) :
    (∫⁻ t in Ioi (0 : ℝ),
       μ {z : ℝ≥0 | t < (z : ℝ)} *
         ENNReal.ofReal (Real.exp (-θ * t))) =
      ∫⁻ z : ℝ≥0,
        ENNReal.ofReal ((1 - Real.exp (-θ * (z : ℝ))) / θ) ∂μ := by
  sorry

end AvramDividend.Classical
