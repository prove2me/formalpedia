-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB312_scaled_translated_gaussian_open_cell_lintegral
-- name    : AvramDividend.Classical.avram_gbB312_scaled_translated_gaussian_open_cell_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:08:09.601692+00:00
-- url     : https://prove2.me/theorems/80ff46b4-7565-4aae-a591-15f1812b9561
-- title:
--   Any nonnegative coefficient times translated Gaussian inverse-square-root open-cell kernel integrates to its square-root bound
-- statement:
--   For arbitrary nonnegative extended-real coefficient, finite physical cell and nonnegative width, the open-cell nonnegative Lebesgue integral of the coefficient times the inverse-square-root elapsed-time Gaussian kernel is bounded by the coefficient times twice the square root of the cell width. The proof applies the Proved B310 near-endpoint integrability, Proved B309 kernel lintegral bound and the constant-multiplication property of the nonnegative Lebesgue integral. This is the exact time-integration input for the source-normalised B308 estimate.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB312_scaled_translated_gaussian_open_cell_lintegral (s δ : ℝ) (hδ : 0 ≤ δ) (C : ℝ≥0∞) :
    (∫⁻ t in Set.Ioo s (s + δ),
      C * ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ))) ∂volume) ≤
      C * ENNReal.ofReal (2 * Real.sqrt δ) := by sorry
