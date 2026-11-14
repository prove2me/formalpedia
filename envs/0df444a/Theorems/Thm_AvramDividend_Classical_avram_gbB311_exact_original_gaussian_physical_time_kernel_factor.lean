-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB311_exact_original_gaussian_physical_time_kernel_factor
-- name    : AvramDividend.Classical.avram_gbB311_exact_original_gaussian_physical_time_kernel_factor
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T00:08:45.101266+00:00
-- url     : https://prove2.me/theorems/8febb75d-9182-4b1d-a063-d5756bafffbf
-- title:
--   Exact original Gaussian source variance factor on a real physical grid equals normal density coefficient times elapsed-time inverse square root
-- statement:
--   For positive source Gaussian volatility, integer refinement and real physical time strictly inside one fourth-power grid cell, the exact original Gaussian inverse standard-deviation expression with its native nonnegative-real elapsed time equals the real Gaussian normalisation coefficient times inverse square root of physical elapsed time. Prove by matching Real.toNNReal time, NNReal subtraction and the Proved B268 source variance factorisation. This is the original pointwise Gaussian-kernel bridge required in B308.

import Mathlib
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB311_exact_original_gaussian_physical_time_kernel_factor (sigma : ℝ) (hsigma : 0 < sigma)
    (m i : ℕ) (hm : 0 < m) (t : ℝ)
    (ht : t ∈ Set.Ioo
      ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))
      (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4)))) :
    (Real.sqrt (2 * Real.pi *
      (((NNReal.mk (sigma ^ 2) (sq_nonneg sigma)) *
        ((Real.toNNReal t -
          ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) : ℝ≥0) : NNReal) : ℝ))))⁻¹ =
      (1 / (sigma * Real.sqrt (2 * Real.pi))) *
        (t - (i : ℝ) * (1 / ((m : ℝ) ^ 4))) ^ (-(1 / 2 : ℝ)) := by sorry
