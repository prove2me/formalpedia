-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_jump_tail_laplace_layercake
-- name    : AvramDividend.Classical.positive_jump_tail_laplace_layercake
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T20:46:53.233467+00:00
-- url     : https://prove2.me/theorems/f880ecdc-214c-4464-8391-cf90fd552256
-- title:
--   Weighted Lévy-tail Laplace identity from the layer-cake formula
-- statement:
--   For any measure on nonnegative jump magnitudes and any positive discount exponent, the nonnegative integral of the discounted kernel accumulated up to each jump magnitude equals the Laplace-weighted integral of its positive tail mass. This is the exact Tonelli/layer-cake step needed in the bounded-variation q-scale-function renewal equation, before evaluating the inner exponential integral. No assumptions about a Lévy process are added.
-- source:
--   Pinned Mathlib MeasureTheory.Integral.Layercake, theorem lintegral_comp_eq_lintegral_meas_lt_mul; BV Lévy tail transform in the Avram/Kyprianou scale-function analysis

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Discounted tail-kernel identity for an arbitrary measure of positive jump
magnitudes; the Tonelli core of the bounded-variation Levy renewal equation. -/
theorem positive_jump_tail_laplace_layercake (μ : Measure ℝ≥0) (θ : ℝ) (hθ : 0 < θ) :
    (∫⁻ z : ℝ≥0,
       ENNReal.ofReal (∫ t in (0 : ℝ)..(z : ℝ), Real.exp (-θ * t)) ∂μ) =
      ∫⁻ t in Ioi (0 : ℝ),
        μ {z : ℝ≥0 | t < (z : ℝ)} *
          ENNReal.ofReal (Real.exp (-θ * t)) := by
  sorry

end AvramDividend.Classical
