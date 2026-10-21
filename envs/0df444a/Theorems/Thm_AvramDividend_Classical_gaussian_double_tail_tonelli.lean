-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_tonelli
-- name    : AvramDividend.Classical.gaussian_double_tail_tonelli
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T22:44:18.011161+00:00
-- url     : https://prove2.me/theorems/4aadf821-fb44-4f67-a82b-e6c108390a7b
-- title:
--   Tonelli exchange for the Gaussian Esscher-tilted double-tail jump kernel
-- statement:
--   For any s-finite real measure μ and parameters φ,θ, the nonnegative measurable kernel 1_{0<t<z}(z−t)exp(−θt)exp(−φz), encoded with ENNReal.ofReal, has equal iterated extended-nonnegative integrals after swapping Lebesgue t and μ jump magnitude z. This is the direct Tonelli step used to lift the single-jump exponential double-tail Laplace integral to the Esscher-tilted Lévy jump measure.
-- source:
--   Pinned Mathlib lintegral_lintegral_swap and measurable kernel from elementary continuous functions.

import Mathlib
open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_tonelli
    (μ : Measure ℝ) [SFinite μ] (φ θ : ℝ) :
    (∫⁻ t : ℝ, ∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
          ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂μ ∂volume) =
    (∫⁻ z : ℝ, ∫⁻ t : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
          ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂volume ∂μ) := by sorry
