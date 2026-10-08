-- Prove2me | Theorems.Thm_AvramDividend_Classical_positiveLaplace_weighted_nnreal_map
-- name    : AvramDividend.Classical.positiveLaplace_weighted_nnreal_map
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T21:26:20.953988+00:00
-- url     : https://prove2.me/theorems/ae778486-6491-4290-aca7-972c7d5e095d
-- title:
--   Laplace transform of a weighted nonnegative measure after coercion to the reals
-- statement:
--   Weight a measure on the nonnegative reals by the nonnegative density max(1-exp(-a z),0), then map it to the real line by the canonical coercion. Its positive exponential Laplace transform at s is the original μ-integral of the exponential test function multiplied by that density. This is a pure measure-transport identity used to construct the tilted bounded-variation renewal kernel.
-- source:
--   Pinned Mathlib MeasureTheory.Integral.Lebesgue.Map theorem lintegral_map and MeasureTheory.Measure.WithDensity theorem lintegral_withDensity_eq_lintegral_mul₀. This isolates the withDensity/map transport in the Avram bounded-variation tilted-renewal construction.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Mapping a weighted measure on nonnegative reals into the real line preserves
the positive exponential Laplace integral, with the density appearing as the
expected multiplicative weight. -/
theorem positiveLaplace_weighted_nnreal_map
    (μ : Measure ℝ≥0) (a s : ℝ) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-s * x))
      ∂Measure.map (fun z : ℝ≥0 => (z : ℝ))
        (μ.withDensity
          (fun z : ℝ≥0 =>
            ENNReal.ofReal (1 - Real.exp (-a * (z : ℝ)))))) =
      ∫⁻ z : ℝ≥0,
        ENNReal.ofReal (Real.exp (-s * (z : ℝ))) *
          ENNReal.ofReal (1 - Real.exp (-a * (z : ℝ))) ∂μ := by
  sorry

end AvramDividend.Classical
