-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_continuous_test_uniform_jump_cell
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_continuous_test_uniform_jump_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:34:09.171622+00:00
-- url     : https://prove2.me/theorems/ba344151-4aba-4aec-86c9-385b2d1adf99
-- title:
--   Continuous negative-jump test converges along the genuine original grid cell
-- statement:
--   For an original càdlàg source path and any continuous test function f, pick the already source-constructed right-closed uniform cell containing an arbitrary original positive jump time. Show the test function of its actual grid increment converges to f evaluated at the genuine source jump mark, retaining the exact cell index and interval constraints. This is the per-jump test-function ingredient of the finite-grid matching proof.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_cell_increment_to_jump
open Filter Set Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_continuous_test_uniform_jump_cell
    (Y : ℝ≥0 → ℝ) (T u : ℝ≥0)
    (hT : 0 < T) (hu : 0 < u) (huT : u ≤ T)
    (hL : Tendsto Y (nhdsWithin u (Iio u))
      (𝓝 (Function.leftLim Y u)))
    (hR : ContinuousWithinAt Y (Ici u) u)
    (f : ℝ → ℝ) (hf : Continuous f) :
    ∃ i : ℕ → ℕ,
      (∀ n, i n ≤ n ∧
        (i n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) < u ∧
        u ≤ ((i n + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ∧
      Tendsto (fun n =>
        f (Y (((i n + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
          Y ((i n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))))
        atTop (𝓝 (f (Y u - Function.leftLim Y u))) := by sorry
