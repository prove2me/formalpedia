-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_finite_distinct_time_endpoints_eventually_injective
-- name    : AvramDividend.Classical.avram_p2_34dbea70_finite_distinct_time_endpoints_eventually_injective
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:42:37.50593+00:00
-- url     : https://prove2.me/theorems/43aea3ea-ba4f-4ae2-a477-d198ee3579ef
-- title:
--   Finitely many distinct jump times have eventually distinct convergent cell endpoints
-- statement:
--   Fix any finite set of nonnegative source times. If for every source time in that finite set an associated sequence of nonnegative right-cell endpoints converges to that source time, then for all sufficiently fine mesh indices the endpoint assignment is injective on the given finite set. This is the finite-subset no-collision step of cadlag jump grid capture and requires no Lévy compensator, jump intensity, finite activity or stochastic process.

import Mathlib

open Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_34dbea70_finite_distinct_time_endpoints_eventually_injective
    (F : Finset ℝ≥0) (b : ℝ≥0 → ℕ → ℝ≥0)
    (hb : ∀ u ∈ F, Tendsto (b u) atTop (𝓝 u)) :
    ∀ᶠ n : ℕ in atTop,
      Set.InjOn (fun u : ℝ≥0 => b u n) (F : Set ℝ≥0) := by sorry
