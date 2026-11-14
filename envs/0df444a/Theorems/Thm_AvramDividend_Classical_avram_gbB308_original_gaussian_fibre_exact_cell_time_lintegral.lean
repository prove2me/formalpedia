-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB308_original_gaussian_fibre_exact_cell_time_lintegral
-- name    : AvramDividend.Classical.avram_gbB308_original_gaussian_fibre_exact_cell_time_lintegral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T00:00:32.342811+00:00
-- url     : https://prove2.me/theorems/edcfeb67-0b70-449f-8cf0-e7f91b2f871b
-- title:
--   Exact original Gaussian source fibre density has fifth-order probability-time mass over a fourth-power cell
-- statement:
--   For positive original Gaussian volatility, a positive fourth-power physical mesh, and one prescribed cell, the time lintegral of the exact original Gaussian B266 small-ball fibre bound with the cubic reciprocal dividend threshold is no greater than twice the reciprocal of volatility, normal sqrt(2pi) constant and fifth power of the mesh refinement. Prove using accepted B268 variance factorisation, B280 translated inverse square-root integral and B303 conversion to nonnegative Lebesgue integration. This analytic estimate is the last deterministic input in the sound source-specific B299 reduction.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB308_original_gaussian_fibre_exact_cell_time_lintegral
    (sigma : ℝ) (hsigma : 0 < sigma)
    (m i : ℕ) (hm : 0 < m) :
    (∫⁻ t in Set.Ioo
        ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))
        (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4))),
      ENNReal.ofReal
        ((Real.sqrt (2 * Real.pi *
          (((NNReal.mk (sigma ^ 2) (sq_nonneg sigma)) *
            ((Real.toNNReal t -
              ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) : ℝ≥0) : NNReal) : ℝ))))⁻¹) *
      ENNReal.ofReal (1 / ((m : ℝ) ^ 3)) ∂volume) ≤
      (Real.toNNReal (2 /
        (sigma * Real.sqrt (2 * Real.pi) * ((m : ℝ) ^ 5))) : ℝ≥0∞) := by sorry
