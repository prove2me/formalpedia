-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_finite_jump_cell_selectors
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_uniform_finite_jump_cell_selectors
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:06:27.176741+00:00
-- url     : https://prove2.me/theorems/b2eb2219-64af-47fe-909d-d0b4023c0625
-- title:
--   Finite original jumps have coherent uniform grid selectors and exact jump-mark limits
-- statement:
--   For every finite set of positive-time original càdlàg jumps in the horizon, choose all uniform half-open mesh cell indices simultaneously and retain both their exact containment and their original path increment convergence to left/right jump marks. This packages the already proved original uniform-cell theorem into a finite family suitable for full-grid compact-test matching without adding probabilistic assumptions.

import Mathlib
open Filter Set Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_uniform_finite_jump_cell_selectors
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (F : Finset ℝ≥0)
    (hpos : ∀ t ∈ F, 0 < t)
    (hbound : ∀ t ∈ F, t ≤ T)
    (hL : ∀ t ∈ F,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t ∈ F, ContinuousWithinAt Y (Ici t) t) :
    ∃ idx : ℝ≥0 → ℕ → ℕ,
      (∀ t ∈ F, ∀ n, idx t n ≤ n ∧
        (idx t n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) < t ∧
        t ≤ (((idx t n + 1 : ℕ) : ℝ≥0) *
          (T / ((n : ℝ≥0) + 1)))) ∧
      (∀ t ∈ F,
        Tendsto (fun n =>
          Y (((idx t n + 1 : ℕ) : ℝ≥0) *
            (T / ((n : ℝ≥0) + 1))) -
          Y ((idx t n : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))
          atTop (𝓝 (Y t - Function.leftLim Y t)))  := by sorry
