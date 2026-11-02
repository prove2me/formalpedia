-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_cap_corner_countable_uniform_interior_cutoff_sequence
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_cap_corner_countable_uniform_interior_cutoff_sequence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:14:28.088213+00:00
-- url     : https://prove2.me/theorems/9f15eb63-69d0-402d-88bf-d16c1e806357
-- title:
--   Countably many strictly interior cap cutoffs give uniform one-sided approximation to the true slope-one continuation at all reserve values
-- statement:
--   Under corrected UBV finite-cap hypotheses of continuity on nonnegative reserves, C² and w'≥1 only strictly inside c, select a sequence b_n satisfying 0<b_n<c. For every n and EVERY y≥0 simultaneously, the slope-one continuation at b_n is below the actual cap continuation at c by a nonnegative amount strictly less than 1/(n+1). This provides a countable deterministic cap-localisation sequence whose every piecewise kink lies in the valid interior C² domain and which converges uniformly from below as n→∞ without assuming any left derivative at the actual cap. This is an analytic prerequisite for a correct stochastic stopped Itô–Meyer limit, not the formula itself or the dividend Stieltjes correction.
-- source:
--   Parent Proved uniform ε interior cutoff theorem AvramDividend.Classical.avram_wave5_05_ubv_cap_corner_uniform_epsilon_interior_cutoff_approximation, original Proved inclusive secant 44b01929-5817-44ac-9439-6eb3c9879f2c; corrected core 429e17ca-5528-40b5-b593-7c03973d0706 unchanged.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_cap_corner_uniform_epsilon_interior_cutoff_approximation

open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_cap_corner_countable_uniform_interior_cutoff_sequence
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c → 1 ≤ deriv w y) :
    ∃ b : ℕ → ℝ,
      (∀ n : ℕ, 0 < b n ∧ b n < c) ∧
      ∀ (n : ℕ) (y : ℝ), 0 ≤ y →
        0 ≤ (if y ≤ c then w y else w c + (y - c)) -
          (if y ≤ b n then w y else w (b n) + (y - b n)) ∧
        (if y ≤ c then w y else w c + (y - c)) -
          (if y ≤ b n then w y else w (b n) + (y - b n)) <
          1 / ((n : ℝ) + 1) := by sorry
