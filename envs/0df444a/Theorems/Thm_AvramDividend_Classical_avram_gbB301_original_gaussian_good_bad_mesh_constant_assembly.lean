-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB301_original_gaussian_good_bad_mesh_constant_assembly
-- name    : AvramDividend.Classical.avram_gbB301_original_gaussian_good_bad_mesh_constant_assembly
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:31:03.024229+00:00
-- url     : https://prove2.me/theorems/fbce36fc-afe2-4312-97d1-961e9896c7c2
-- title:
--   Localised bad dividend variation and Gaussian good-cell mass fit the original finite-cap inverse mesh coefficient
-- statement:
--   For positive Gaussian volatility, finite horizon, dividend-variation bound and mesh refinement, the sum of the exact original bad-cell bound M/m and normal-density good-cell bound A/m does not exceed the original B276b coefficient (1+M+A)/m in nonnegative extended-real arithmetic. A is the original source Gaussian factor 2n divided by volatility times sqrt 2pi. This is the numerical assembly needed to close B276b from B296, B290, B297 and B298.

import Mathlib
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB301_original_gaussian_good_bad_mesh_constant_assembly (sigma : ℝ) (hsigma : 0 < sigma)
    (n M m : ℕ) (hm : 0 < m) :
    ENNReal.ofReal ((M : ℝ) / (m : ℝ)) +
      (Real.toNNReal ((2 * (n : ℝ)) /
        (sigma * Real.sqrt (2 * Real.pi))) : ℝ≥0∞) *
        (m : ℝ≥0∞)⁻¹ ≤
      (Real.toNNReal (1 + (M : ℝ) +
        (2 * (n : ℝ)) / (sigma * Real.sqrt (2 * Real.pi))) : ℝ≥0∞) *
        (m : ℝ≥0∞)⁻¹ := by sorry
