-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_measure_atom_transform
-- name    : AvramDividend.Classical.gaussian_double_tail_measure_atom_transform
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T07:03:00.875708+00:00
-- url     : https://prove2.me/theorems/b0cd3585-b3f9-4e36-8064-6673645be20a
-- title:
--   Measure-integrated Esscher Gaussian double-tail atom transform
-- statement:
--   For an s-finite positive jump-magnitude measure μ and φ>0, θ≥0, multiplying the z-first double-tail iterated ENNReal integral by θ² equals the positive-jump integral of exp(−φz)(exp(−θz)−1+θz). Prove it by reducing each fixed-z inner integral to the previously established Esscher-weighted ENNReal single-atom identity, applying measurability of parameterised lintegrals, moving a constant through the outer lintegral, and identifying the positive-half-line indicator. This is the measure-level z-first side of the shifted Lévy–Khintchine double-tail transform.
-- source:
--   Proved gaussian_double_tail_atom_esscher_lintegral once accepted; pinned Measurable.lintegral_prod_left, lintegral_indicator, lintegral_const_mul.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_measure_atom_transform
    (μ : Measure ℝ) [SFinite μ] (φ θ : ℝ)
    (hφ : 0 < φ) (hθ : 0 ≤ θ) :
    ENNReal.ofReal (θ ^ 2) *
      (∫⁻ z : ℝ, ∫⁻ t : ℝ,
        (if 0 < t ∧ t < z then
          ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
            ENNReal.ofReal (Real.exp (-φ * z))
         else 0) ∂volume ∂μ) =
      (∫⁻ z in Ioi (0 : ℝ),
        ENNReal.ofReal
          (Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z)) ∂μ) := by sorry
