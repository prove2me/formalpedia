-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f6_hjb_finite_clock_budget_to_full
-- name    : AvramDividend.Classical.avram_p4_f6_hjb_finite_clock_budget_to_full
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T10:22:54.014027+00:00
-- url     : https://prove2.me/theorems/6e73a32f-d040-4b38-9f62-623b4cd1e085
-- title:
--   Finite killed upper-first clock budgets imply the full upper-first clock budget
-- statement:
--   Let u and d be measurable first-passage clocks and v a measurable nonnegative discounted reward. If the expected upper-before-lower reward, truncated at every natural-number horizon, satisfies a uniform real-valued weighted budget with nonnegative coefficient and upper bound, then the same budget holds for the untruncated upper-before-lower reward. This is the exact conditional measure-theoretic finite-to-full step in the original HJB upcross proof, and it delegates the genuinely stochastic estimate to a separate child.
-- source:
--   Original upcross HJB P4-F6 finite-to-infinite-horizon reduction for 8d1164b7 and 1122a786. No stochastic estimate assumed implicitly: requires explicit uniform finite-clock reward bound.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f6_hjb_finite_clock_budget_to_full
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (u d v : Ω → ℝ≥0∞)
    (hu : Measurable u) (hd : Measurable d) (hv : Measurable v)
    (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hfinite : ∀ n : ℕ,
      a * (∫⁻ ω, if u ω < d ω ∧ u ω ≤ (n : ℝ≥0∞) then v ω else 0 ∂P).toReal ≤ c) :
    a * (∫⁻ ω, if u ω < d ω then v ω else 0 ∂P).toReal ≤ c := by sorry
