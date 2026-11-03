-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_local_left_grid_samples_recover_left_limit
-- name    : AvramDividend.Classical.avram_wave7_01_local_left_grid_samples_recover_left_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:10:42.646746+00:00
-- url     : https://prove2.me/theorems/255952bb-3a58-4f25-9db9-65dcabf78736
-- title:
--   Path-local left-grid convergence with no impossible time-zero requirement
-- statement:
--   For a single original real coordinate path and fixed nonnegative time, if left-grid samples lie strictly below that time and squeeze to it, their values converge to the true left limit. The bounds are local to the specified path, allowing a globally defined measurable selector to have a harmless zero-time fallback.
-- source:
--   Squeeze selected grid times between lower and constant τ, derive convergence in nhdsWithin(Iio τ), and compose with the supplied left-limit Tendsto.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_local_left_grid_samples_recover_left_limit
    (grid : ℕ → ℝ≥0) (Y : ℝ≥0 → ℝ) (τ : ℝ≥0)
    (lower : ℕ → ℝ≥0) (index : ℕ → ℕ)
    (hBounds : ∀ n : ℕ, lower n ≤ grid (index n) ∧
      grid (index n) < τ)
    (hLower : Tendsto lower atTop (𝓝 τ))
    (hLeft : Tendsto Y (𝓝[<] τ) (𝓝 (Function.leftLim Y τ))) :
    Tendsto (fun n : ℕ => Y (grid (index n)))
      atTop (𝓝 (Function.leftLim Y τ)) := by sorry
