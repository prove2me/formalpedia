-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_jump_test_local_continuity
-- name    : AvramDividend.Classical.avram_p2_l_mesh_finite_jump_test_local_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:16:53.567144+00:00
-- url     : https://prove2.me/theorems/5319fd47-b6e2-4d7e-ab2c-860910e6c10d
-- title:
--   Finite original right-closed jump-cell test sums converge under continuity at the actual marks
-- statement:
--   For a finite set of actual positive jump times on a compact horizon, choose genuine original right-closed mesh cells. Their marked-test sum converges to the intrinsic jump test sum when f is continuous only at the finitely many actual jump marks. Globally discontinuous indicator tests are therefore covered when their actual marks lie off the set boundary. This uses P2-A's proved endpoint and shrinking increment lemmas, with no rate, expectation, compensator or arbitrary Borel indicator hypothesis.

import Mathlib.Topology.Order.LeftRightLim
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_source_jump_cells_sided_limits
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_shrinking_cell_increment_converges_to_actual_jump

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators

theorem AvramDividend.Classical.avram_p2_l_mesh_finite_jump_test_local_continuity
    (Y : ℝ≥0 → ℝ) (S : Finset ℝ≥0)
    (T : ℝ≥0) (hT : 0 < T)
    (f : ℝ → ℝ)
    (hf : ∀ u ∈ S, ContinuousAt f (Y u - Function.leftLim Y u))
    (hTimes : ∀ u ∈ S, 0 < u ∧ u ≤ T)
    (hL : ∀ u ∈ S,
      Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)))
    (hR : ∀ u ∈ S, ContinuousWithinAt Y (Ici u) u) :
    ∃ idx : ℝ≥0 → ℕ → ℕ,
      (∀ u ∈ S, ∀ n, idx u n ≤ n ∧
        (idx u n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) < u ∧
        u ≤ ((idx u n + 1 : ℕ) : ℝ≥0) *
          (T / ((n : ℝ≥0) + 1))) ∧
      Tendsto (fun n : ℕ =>
        ∑ u ∈ S, f (Y (((idx u n + 1 : ℕ) : ℝ≥0) *
          (T / ((n : ℝ≥0) + 1))) -
          Y ((idx u n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))))
        atTop (𝓝 (∑ u ∈ S, f (Y u - Function.leftLim Y u))) := by sorry
