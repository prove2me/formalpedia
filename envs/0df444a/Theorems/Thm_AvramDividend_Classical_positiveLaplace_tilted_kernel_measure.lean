-- Prove2me | Theorems.Thm_AvramDividend_Classical_positiveLaplace_tilted_kernel_measure
-- name    : AvramDividend.Classical.positiveLaplace_tilted_kernel_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T21:46:13.575162+00:00
-- url     : https://prove2.me/theorems/9fc5f28e-65c3-497b-a148-87b8847d7d5e
-- title:
--   Laplace transform of the positive tilted bounded-variation renewal kernel
-- statement:
--   For an s-finite positive jump-magnitude measure μ, nonnegative tilt a and positive discount s, define the tilted BV renewal kernel as the sum of (i) the positive jump-tail density measure and (ii) the positive-half-line cumulative density measure associated with μ weighted by 1-exp(-a z). Its positive exponential Laplace transform is exactly ∫(1-exp(-(s+a)z))/s dμ(z).
-- source:
--   Composition target for AvramDividend.Classical.positive_laplace_tail_withDensity, positiveLaplace_weighted_cumulative_nnreal, positive_tilted_kernel_pointwise_identity, and pinned Mathlib lintegral_add_measure/withDensity APIs. This is the exact K_a transform needed for the bounded-variation tilted renewal construction.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- The positive BV tilted renewal kernel, formed from the jump-tail density plus the cumulative density of the exponentially weighted jump-magnitude measure, has shifted compensator Laplace transform. -/
theorem positiveLaplace_tilted_kernel_measure
    (μ : Measure ℝ≥0) [SFinite μ]
    (a s : ℝ) (ha : 0 ≤ a) (hs : 0 < s) :
    let tailMeasure : Measure ℝ :=
      (volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun t : ℝ => μ {z : ℝ≥0 | t < (z : ℝ)})
    let weightedMeasure : Measure ℝ :=
      Measure.map (fun z : ℝ≥0 => (z : ℝ))
        (μ.withDensity
          (fun z : ℝ≥0 =>
            ENNReal.ofReal (1 - Real.exp (-a * (z : ℝ)))))
    let cumulativeMeasure : Measure ℝ :=
      (volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => weightedMeasure (Iic x))
    let κ : Measure ℝ := tailMeasure + cumulativeMeasure
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-s * x)) ∂κ) =
      ∫⁻ z : ℝ≥0,
        ENNReal.ofReal
          ((1 - Real.exp (-(s + a) * (z : ℝ))) / s) ∂μ := by
  sorry

end AvramDividend.Classical
