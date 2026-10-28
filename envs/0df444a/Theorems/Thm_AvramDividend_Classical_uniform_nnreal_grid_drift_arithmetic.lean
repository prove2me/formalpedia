-- Prove2me | Theorems.Thm_AvramDividend_Classical_uniform_nnreal_grid_drift_arithmetic
-- name    : AvramDividend.Classical.uniform_nnreal_grid_drift_arithmetic
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T14:59:19.494519+00:00
-- url     : https://prove2.me/theorems/e00d24d4-352f-4361-b8a7-144beb710412
-- title:
--   Uniform nonnegative time grid exactly matches real-valued drift increments and horizon threshold
-- statement:
--   On a uniform grid in NNReal, each real-valued drift increment d(t_(k+1)-t_k) is exactly dδ and the count-rescaled cell threshold N dδ equals dT. This connects the proven grid construction with the actual Lévy drift-deficit probability bound, preserving exact time arithmetic.
-- source:
--   Uniform grid and NNReal cast arithmetic, in service of Avram et al. (2007) §3.3 finite-activity zero-barrier case.

import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Ring
open scoped NNReal

theorem AvramDividend.Classical.uniform_nnreal_grid_drift_arithmetic
    (d : ℝ) (T δ : ℝ≥0) (N : ℕ) (ts : ℕ → ℝ≥0)
    (hStep : ∀ k : ℕ, k < N → ts k ≤ ts (k + 1))
    (hSpacing : ∀ k : ℕ, k < N → ts (k + 1) - ts k = δ)
    (hLength : (N : ℝ≥0) * δ = T) :
    (∀ k : ℕ, k < N →
      d * ((ts (k + 1) : ℝ) - (ts k : ℝ)) = d * (δ : ℝ)) ∧
    (N : ℝ) * (d * (δ : ℝ)) = d * (T : ℝ) := by sorry
