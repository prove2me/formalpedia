-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_selected_right_endpoint_squeeze
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_selected_right_endpoint_squeeze
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:11:08.550562+00:00
-- url     : https://prove2.me/theorems/efb8ae33-6127-4626-b4d3-fcfb9a0440e7
-- title:
--   Selected original grid right endpoints converge by a vanishing-width squeeze
-- statement:
--   An exact order-topological squeeze for source mesh right endpoints: if a mesh endpoint lies between the original jump time and that time plus the vanishing width, then it converges to the jump time. This supplies the endpoint-convergence hypothesis needed to prove eventual distinctness of selected uniform cells for different true jumps.

import Mathlib
open Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_selected_right_endpoint_squeeze
    (u : ℝ≥0) (r w : ℕ → ℝ≥0)
    (hr : ∀ n, u ≤ r n ∧ r n ≤ u + w n)
    (hw : Tendsto w atTop (𝓝 (0 : ℝ≥0))) :
    Tendsto r atTop (𝓝 u)  := by sorry
