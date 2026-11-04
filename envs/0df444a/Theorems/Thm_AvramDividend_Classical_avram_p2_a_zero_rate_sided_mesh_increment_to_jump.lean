-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_sided_mesh_increment_to_jump
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_sided_mesh_increment_to_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:07:19.852587+00:00
-- url     : https://prove2.me/theorems/6f2a6f8d-4f04-4db4-bce6-f0d26b235132
-- title:
--   Original càdlàg sided-grid increments converge exactly to the jump mark
-- statement:
--   For any càdlàg real-valued path at a fixed positive-time jump, if left mesh endpoints approach the time strictly from below and right endpoints from above, prove directly from the given left limit and right continuity that the mesh increment converges to the true jump. This is an exact deterministic interface in the genuine original-source marked test-grid convergence, with no Lévy rate or compensator.

import Mathlib

open Filter Set Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_sided_mesh_increment_to_jump
    (Y : ℝ≥0 → ℝ) (u : ℝ≥0)
    (hL : Tendsto Y (nhdsWithin u (Iio u))
      (𝓝 (Function.leftLim Y u)))
    (hR : ContinuousWithinAt Y (Ici u) u)
    (l r : ℕ → ℝ≥0)
    (hl : Tendsto l atTop (nhdsWithin u (Iio u)))
    (hr : Tendsto r atTop (nhdsWithin u (Ici u))) :
    Tendsto (fun n => Y (r n) - Y (l n))
      atTop (𝓝 (Y u - Function.leftLim Y u)) := by sorry
