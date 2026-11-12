-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_uniform_floor_samples_converge_from_left
-- name    : AvramDividend.Classical.avram_bvb_b21_original_uniform_floor_samples_converge_from_left
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:29:54.935512+00:00
-- url     : https://prove2.me/theorems/a1348452-5427-4590-ba14-cf4e9d35ad19
-- title:
--   Exact original uniform-grid floor samples converge from below
-- statement:
--   The genuine source grid of width T/(n+2) has a canonical floor-index sample at or to the left of every nonnegative time, and this left sample converges to that time as the grid refines. This rules out the non-refining and fixed-point-sampling substitutes.
-- source:
--   Necessary explicit sample-convergence input to the source-exact original BV one-sided marked compensator quadrature, which relies on reserve left-limit continuity.

import Mathlib
open Filter
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b21_original_uniform_floor_samples_converge_from_left
    (T t : ℝ) (hT : 0 < T) (ht : 0 ≤ t) :
    (∀ n : ℕ,
      T * (⌊(t / T) * ((n : ℝ) + 2)⌋₊ : ℝ) / ((n : ℝ) + 2) ≤ t) ∧
    Tendsto
      (fun n : ℕ => T * (⌊(t / T) * ((n : ℝ) + 2)⌋₊ : ℝ) /
        ((n : ℝ) + 2))
      atTop (𝓝 t) := by sorry
