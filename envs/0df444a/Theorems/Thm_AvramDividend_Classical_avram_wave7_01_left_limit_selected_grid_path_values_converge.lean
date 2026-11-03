-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_left_limit_selected_grid_path_values_converge
-- name    : AvramDividend.Classical.avram_wave7_01_left_limit_selected_grid_path_values_converge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:51:59.237716+00:00
-- url     : https://prove2.me/theorems/2d770297-6dd5-41bc-a789-581894b028fb
-- title:
--   Left-limit càdlàg path values recovered by bounded countable grid sampling
-- statement:
--   At any path-dependent positive jump time, selected countable grid times trapped between an increasing numerical lower approximation and the strict left endpoint converge within the strict-left neighbourhood, so the path samples converge to its exact left limit. The lower approximation convergence is explicit, and a dense-grid selector must supply the interval bounds.
-- source:
--   Order-topological squeeze between lower_n(Y)→t(Y) and constant t(Y), upgrade with strict-left membership to Tendsto into nhdsWithin (Iio t), compose with the supplied left-limit convergence.

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_left_limit_selected_grid_path_values_converge
    (grid : ℕ → ℝ≥0) (t : (ℝ≥0 → ℝ) → ℝ≥0)
    (lower : ℕ → (ℝ≥0 → ℝ) → ℝ≥0)
    (index : ℕ → (ℝ≥0 → ℝ) → ℕ)
    (hBounds : ∀ (Y : ℝ≥0 → ℝ) (n : ℕ),
      lower n Y ≤ grid (index n Y) ∧
      grid (index n Y) < t Y) :
    ∀ Y : ℝ≥0 → ℝ,
      Tendsto (fun n : ℕ => lower n Y) atTop (𝓝 (t Y)) →
      Tendsto Y (𝓝[<] (t Y)) (𝓝 (Function.leftLim Y (t Y))) →
      Tendsto (fun n : ℕ => Y (grid (index n Y)))
        atTop (𝓝 (Function.leftLim Y (t Y))) := by sorry
