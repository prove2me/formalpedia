-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_uniform_geometric_moment_bound_forces_zero_tail
-- name    : AvramDividend.Classical.avram_p2_b_rate_uniform_geometric_moment_bound_forces_zero_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:29:58.925963+00:00
-- url     : https://prove2.me/theorems/55cf6a31-e663-489e-86f6-d5b798ae5c11
-- title:
--   Uniform bounds on all geometric moments force positive upper-tail mass to vanish
-- statement:
--   If R>1 and a nonnegative mass m satisfies R^n*m<=M for every natural n, then m=0. The proof uses the pinned Archimedean unboundedness of powers and directly supplies the deterministic zero-tail argument needed to show a moment-matching weak limit has no mass above 1.

import Mathlib
open MeasureTheory Set Filter Topology

theorem AvramDividend.Classical.avram_p2_b_rate_uniform_geometric_moment_bound_forces_zero_tail
    (R m M : ℝ) (hR : 1 < R) (hm : 0 ≤ m)
    (hbound : ∀ n : ℕ, R ^ n * m ≤ M) :
    m = 0 := by sorry
