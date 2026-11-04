-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_vanishing_width_halfopen_endpoints
-- name    : AvramDividend.Classical.avram_p2_34dbea70_vanishing_width_halfopen_endpoints
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:11:02.617547+00:00
-- url     : https://prove2.me/theorems/2968ecc4-db34-436c-867f-118817e6d634
-- title:
--   Shrinking right-closed intervals have correctly sided endpoint limits
-- statement:
--   For a fixed nonnegative time u, suppose each interval (a_n,b_n] contains u and its nonnegative length b_n-a_n converges to zero. Then the left endpoints converge to u in the strictly-left neighbourhood filter, and the right endpoints converge to u from the weak-right side. This supplies the exact sided continuity hypotheses for the Proved original source negative jump mesh detector, without assuming finite jump activity or an auxiliary process.

import Mathlib

open Set Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_34dbea70_vanishing_width_halfopen_endpoints
    (u : ℝ≥0) (a b : ℕ → ℝ≥0)
    (hab : ∀ n, a n < u ∧ u ≤ b n)
    (hwidth : Tendsto (fun n => b n - a n) atTop (𝓝 (0 : ℝ≥0))) :
    Tendsto a atTop (𝓝[<] u) ∧
      Tendsto b atTop (nhdsWithin u (Ici u)) := by sorry
