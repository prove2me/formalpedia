-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB103_uniform_mesh_left_approximation_squeeze
-- name    : AvramDividend.Classical.avram_gbB103_uniform_mesh_left_approximation_squeeze
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:33:55.34703+00:00
-- url     : https://prove2.me/theorems/a7917065-2539-4595-a032-f78231da70cd
-- title:
--   Uniform-mesh left endpoints converge under the exact one-cell gap bound
-- statement:
--   A sequence of original uniform partition left endpoints remains at or before a fixed time and has gap bounded by the original horizon divided by m+1; the grid size tends to zero so the left endpoints tend to the fixed time. This deterministic squeeze lemma feeds the source-exact B102 left-grid coefficient convergence without replacing its grid.

import Mathlib
open Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB103_uniform_mesh_left_approximation_squeeze
    (n : ℕ) (hn : 0 < n) (t : ℝ)
    (s : ℕ → ℝ)
    (hLeft : ∀ m, s m ≤ t)
    (hGap : ∀ m, t - s m ≤ (n : ℝ) / ((m : ℝ) + 1)) :
    Tendsto s atTop (𝓝 t) := by sorry
