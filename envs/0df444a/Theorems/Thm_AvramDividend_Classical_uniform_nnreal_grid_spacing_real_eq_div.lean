-- Prove2me | Theorems.Thm_AvramDividend_Classical_uniform_nnreal_grid_spacing_real_eq_div
-- name    : AvramDividend.Classical.uniform_nnreal_grid_spacing_real_eq_div
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T15:19:49.180265+00:00
-- url     : https://prove2.me/theorems/be8db81d-62bb-4957-bb28-70b6977ae605
-- title:
--   Exact NNReal grid cell duration equals real horizon divided by positive cell count
-- statement:
--   If N>0 and Nδ=T in nonnegative real time, then the real-valued step duration equals T/N. This cast bridge is needed to substitute the exact cell length into the finite-activity Lévy small-time exponential probability bound.
-- source:
--   Exact NNReal-to-real mesh arithmetic in Avram et al. (2007), §3.3 first-jump valuation.

import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Ring
open scoped NNReal

theorem AvramDividend.Classical.uniform_nnreal_grid_spacing_real_eq_div
    (T δ : ℝ≥0) (N : ℕ) (hN : 0 < N)
    (hTotal : (N : ℝ≥0) * δ = T) :
    (δ : ℝ) = (T : ℝ) / (N : ℝ) := by sorry
