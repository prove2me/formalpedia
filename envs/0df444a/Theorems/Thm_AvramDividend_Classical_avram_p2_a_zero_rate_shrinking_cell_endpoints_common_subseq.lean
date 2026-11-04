-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_shrinking_cell_endpoints_common_subseq
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_shrinking_cell_endpoints_common_subseq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:23:36.542397+00:00
-- url     : https://prove2.me/theorems/64efa903-3814-4e19-b15a-0e6a95f39f04
-- title:
--   Shrinking original nonnegative mesh cells have a common subsequential endpoint limit
-- statement:
--   Let the left and right endpoints of arbitrary original uniform-mesh cells satisfy 0≤a_n≤b_n≤a_n+w_n, with a_n≤T and cell widths w_n→0. Prove that a strictly increasing subsequence of grid indices makes both endpoints converge to the same time t in [0,T]. Use the actual bounded original-time interval compactness and the order-topological squeeze theorem; do not assume any jump count, compensator or intensity statement. This is the core subsequence extraction for ruling out spurious large cells.

import Mathlib
open Set Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_shrinking_cell_endpoints_common_subseq
    (T : ℝ≥0) (a b w : ℕ → ℝ≥0)
    (haT : ∀ n, a n ≤ T)
    (hab : ∀ n, a n ≤ b n)
    (hbw : ∀ n, b n ≤ a n + w n)
    (hw : Tendsto w atTop (𝓝 (0 : ℝ≥0))) :
    ∃ t : ℝ≥0, t ∈ Icc (0 : ℝ≥0) T ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n : ℕ => a (φ n)) atTop (𝓝 t) ∧
        Tendsto (fun n : ℕ => b (φ n)) atTop (𝓝 t) := by sorry
