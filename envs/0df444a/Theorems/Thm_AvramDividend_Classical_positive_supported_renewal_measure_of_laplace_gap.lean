-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_supported_renewal_measure_of_laplace_gap
-- name    : AvramDividend.Classical.positive_supported_renewal_measure_of_laplace_gap
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:14:24.236458+00:00
-- url     : https://prove2.me/theorems/f5d3ec89-859f-4aad-9619-3c8e2a03116c
-- title:
--   Supported geometric renewal measure from a strict positive-kernel Laplace gap
-- statement:
--   Given a positive s-finite measure kernel κ supported on [0,∞), a finite positive scale δ, and one positive Laplace parameter s at which the kernel transform r is strictly below δ, form recursive convolution powers from Dirac mass at zero and the geometric renewal sum β=Σ δ^{-(n+1)} κ^{*n}. Then β remains supported on [0,∞), has the exact geometric Laplace transform δ^{-1}/(1-δ^{-1}r), finite cumulative mass on every lower interval and positive mass at zero. This combines the already proved geometric-renewal transform package with the elementary facts that convolution and countable positive sums preserve nonnegative support.
-- source:
--   Proved AvramDividend.Classical.positive_geometric_renewal_measure_package; pinned Mathlib Measure.conv, Measure.sum_apply and s-finite convolution; direct nonnegative-support argument from product-measure almost-everywhere nonnegativity.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.positive_supported_renewal_measure_of_laplace_gap
    (κ : Measure ℝ) [SFinite κ]
    (hκsupp : κ (Iio (0 : ℝ)) = 0)
    (δ r : ℝ≥0∞) (hδ : 0 < δ) (hδfin : δ ≠ ⊤) (hr : r < δ)
    (s : ℝ) (hs : 0 < s)
    (hκ : (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-s * x)) ∂κ) = r) :
    ∃ β : Measure ℝ,
      β (Iio (0 : ℝ)) = 0 ∧
      (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-s * x)) ∂β) =
          δ⁻¹ * (1 - δ⁻¹ * r)⁻¹ ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      0 < β {0} := by sorry
