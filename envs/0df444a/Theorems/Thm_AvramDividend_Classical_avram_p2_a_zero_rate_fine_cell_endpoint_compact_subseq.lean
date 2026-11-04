-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_fine_cell_endpoint_compact_subseq
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_fine_cell_endpoint_compact_subseq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:22:17.307287+00:00
-- url     : https://prove2.me/theorems/21a46f4a-1902-42ee-a142-a6b38d11a997
-- title:
--   Bounded nonnegative original grid endpoints admit a convergent increasing subsequence
-- statement:
--   For every genuine uniform-grid endpoint sequence bounded in [0,T], extract a strictly increasing sequence of mesh indices along which endpoints converge to some time t in [0,T]. This is a compactness ingredient for proving that a large increment on arbitrarily fine cells must converge to an actual càdlàg jump, without any compensator or Lévy-rate premise.

import Mathlib
open Set Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_fine_cell_endpoint_compact_subseq
    (T : ℝ≥0) (a : ℕ → ℝ≥0) (ha : ∀ n, a n ≤ T) :
    ∃ t : ℝ≥0, t ∈ Icc (0 : ℝ≥0) T ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n : ℕ => a (φ n)) atTop (𝓝 t) := by sorry
