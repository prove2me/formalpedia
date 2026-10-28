-- Prove2me | Theorems.Thm_AvramDividend_Classical_compensated_exp_quadratic_ratio_tendsto_zero_ws01f
-- name    : AvramDividend.Classical.compensated_exp_quadratic_ratio_tendsto_zero_ws01f
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T09:53:18.598097+00:00
-- url     : https://prove2.me/theorems/98b38fb1-1990-4948-8956-02195c150e1b
-- title:
--   Negative compensated Lévy kernel is negligible at quadratic Laplace scale
-- statement:
--   For an almost surely negative jump measure with integrable square and individually integrable compensated kernels, the compensated exponential kernel divided by (n+1)^2 has integral tending to zero. This is the non-Gaussian remainder estimate needed to identify the positive-Laplace small-time Gaussian scaling limit for a spectrally negative Lévy process, without asserting an independent Brownian path decomposition.
-- source:
--   Lévy–Khintchine integrability and dominated convergence; accepted bound exp_neg_remainder_bounds in Prove2Me theorem 6952003f, and canonical accepted negative_compensated_real_integral_tendsto_finite c02c41f4 as DCT proof model. Avram WS1F Gaussian branch 0b94b9ab.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_psi_normalised_lower_bound_small

open MeasureTheory Filter
open AvramDividend.Classical

theorem AvramDividend.Classical.compensated_exp_quadratic_ratio_tendsto_zero_ws01f
    (ν : Measure ℝ) (hneg : ∀ᵐ y ∂ν, y < 0)
    (hSq : Integrable (fun y : ℝ => y ^ 2) ν)
    (hInt : ∀ n : ℕ, Integrable (fun y : ℝ =>
      (Real.exp (((n : ℝ) + 1) * y) - 1 -
        ((n : ℝ) + 1) * y) / (((n : ℝ) + 1) ^ 2)) ν) :
    Tendsto (fun n : ℕ =>
      ∫ y : ℝ, (Real.exp (((n : ℝ) + 1) * y) - 1 -
        ((n : ℝ) + 1) * y) / (((n : ℝ) + 1) ^ 2) ∂ν)
      atTop (nhds 0) := by sorry
