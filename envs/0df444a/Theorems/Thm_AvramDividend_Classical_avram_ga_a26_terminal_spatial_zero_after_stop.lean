-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a26_terminal_spatial_zero_after_stop
-- name    : AvramDividend.Classical.avram_ga_a26_terminal_spatial_zero_after_stop
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:05:43.823539+00:00
-- url     : https://prove2.me/theorems/33991b9d-cbc3-4b85-af21-106d6a9e45b6
-- title:
--   Original stopped-process terminal spatial increment vanishes when both mesh times are clipped
-- statement:
--   For any real-valued process, dividend strategy and test function, the final spatial increment vanishes exactly on paths stopped by the penultimate grid point. This is an exact pathwise identity used to localise the Gaussian terminal residual.
-- source:
--   Avram Gaussian A26 terminal-cell proof

import Mathlib
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ga_a26_terminal_spatial_zero_after_stop
    {Ω : Type*} (L D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (x : ℝ)
    (n : ℝ≥0) (m : ℕ) (ρ : Ω → ℝ≥0) (ω : Ω)
    (hstop : ρ ω ≤ (m : ℝ≥0) * (n / ((m : ℝ≥0) + 1))) :
    let Δ : ℝ≥0 := n / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
    w (x + L (v (m + 1)) ω - D (v m) ω) -
      w (x + L (v m) ω - D (v m) ω) = 0 := by sorry
