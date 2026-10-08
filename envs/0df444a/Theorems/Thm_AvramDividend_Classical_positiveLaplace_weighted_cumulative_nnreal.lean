-- Prove2me | Theorems.Thm_AvramDividend_Classical_positiveLaplace_weighted_cumulative_nnreal
-- name    : AvramDividend.Classical.positiveLaplace_weighted_cumulative_nnreal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T21:31:28.057497+00:00
-- url     : https://prove2.me/theorems/1c39f20f-c683-465c-8a60-f2dc8a62dd02
-- title:
--   Laplace transform of the cumulative of a weighted nonnegative measure
-- statement:
--   For an s-finite measure μ on nonnegative reals, weight μ by the nonnegative density max(1-exp(-a z),0), push the resulting measure into the real line, and let β((-∞,x]) be its cumulative mass. For s>0, the positive Laplace transform of that cumulative over x>0 equals 1/s times the original weighted Laplace transform. The pushed-forward measure has no mass below zero automatically.
-- source:
--   Composition of the published AvramDividend.Classical.positiveLaplace_cumulative_measure with positiveLaplace_weighted_nnreal_map, plus pinned Mathlib Measure.map_apply and the automatic SFinite instances for withDensity and map. This is the cumulative weighted-jump term in the bounded-variation tilted renewal kernel.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Weight a measure on ℝ≥0, map it into ℝ, and take its lower cumulative
function. The positive Laplace transform of that cumulative is the weighted
Laplace transform of the original measure divided by the discount. -/
theorem positiveLaplace_weighted_cumulative_nnreal
    (μ : Measure ℝ≥0) [SFinite μ] (a s : ℝ) (hs : 0 < s) :
    let β : Measure ℝ :=
      Measure.map (fun z : ℝ≥0 => (z : ℝ))
        (μ.withDensity
          (fun z : ℝ≥0 =>
            ENNReal.ofReal (1 - Real.exp (-a * (z : ℝ)))))
    (∫⁻ x : ℝ in Ioi 0,
      ENNReal.ofReal (Real.exp (-s * x)) * β (Iic x)) =
      ENNReal.ofReal (1 / s) *
        (∫⁻ z : ℝ≥0,
          ENNReal.ofReal (Real.exp (-s * (z : ℝ))) *
            ENNReal.ofReal (1 - Real.exp (-a * (z : ℝ))) ∂μ) := by
  sorry

end AvramDividend.Classical
