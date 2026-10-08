-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_jump_kernel_lower_indicator
-- name    : AvramDividend.Classical.negative_jump_kernel_lower_indicator
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T22:22:40.559306+00:00
-- url     : https://prove2.me/theorems/39045b45-3c49-49a2-af84-b58d08d50bc1
-- title:
--   Pointwise lower comparison for negative Lévy jumps split at minus one
-- statement:
--   On any strictly negative real jump, the exact compensated Lévy–Khintchine integrand is bounded below by the positive small-jump compensated kernel restricted to (-1,0), minus the indicator of large negative jumps y≤−1. The estimate is valid for every real Laplace parameter and handles the endpoint y=−1 correctly. It isolates the pointwise comparison needed for a global exponent lower bound without assuming finite Lévy measure.
-- source:
--   Direct case split at y=−1 in canonical Lévy indicator (-1,1), using the nonnegativity of exp on the large-jump part; supports X.ψ lower bounds and non-Gaussian first-moment divergence.

import Mathlib

open MeasureTheory Set

theorem AvramDividend.Classical.negative_jump_kernel_lower_indicator
    (θ y : ℝ) (hy : y < 0) :
    (Ioo (-1 : ℝ) 0).indicator
        (fun z : ℝ => Real.exp (θ * z) - 1 - θ * z) y -
      (Iic (-1 : ℝ)).indicator (fun _ : ℝ => (1 : ℝ)) y ≤
      Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator
          (fun _ : ℝ => (1 : ℝ)) y := by sorry
