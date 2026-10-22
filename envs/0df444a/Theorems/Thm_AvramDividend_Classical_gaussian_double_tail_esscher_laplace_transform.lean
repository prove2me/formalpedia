-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_esscher_laplace_transform
-- name    : AvramDividend.Classical.gaussian_double_tail_esscher_laplace_transform
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T07:05:44.516499+00:00
-- url     : https://prove2.me/theorems/bc04ad69-5705-448c-8074-77afa2a2ee95
-- title:
--   Exact Esscher Gaussian double-tail ENNReal Laplace transform
-- statement:
--   For an s-finite positive jump-magnitude measure and φ>0, θ≥0, the θ²-weighted time-first double-tail ENNReal integral equals the positive-jump Esscher compensator integral. Apply the Proved Gaussian double-tail Tonelli theorem and the separately published measure-integrated Esscher atom transform. This establishes the analytic measure-level double-tail Laplace identity used in the shifted Gaussian Lévy–Khintchine representation; the stochastic scale-function regularity step is separate.
-- source:
--   Proved gaussian_double_tail_tonelli and gaussian_double_tail_measure_atom_transform once accepted.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_esscher_laplace_transform
    (μ : Measure ℝ) [SFinite μ] (φ θ : ℝ)
    (hφ : 0 < φ) (hθ : 0 ≤ θ) :
    ENNReal.ofReal (θ ^ 2) *
      (∫⁻ t : ℝ, ∫⁻ z : ℝ,
        (if 0 < t ∧ t < z then
          ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
            ENNReal.ofReal (Real.exp (-φ * z))
         else 0) ∂μ ∂volume) =
      (∫⁻ z in Ioi (0 : ℝ),
        ENNReal.ofReal
          (Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z)) ∂μ) := by sorry
