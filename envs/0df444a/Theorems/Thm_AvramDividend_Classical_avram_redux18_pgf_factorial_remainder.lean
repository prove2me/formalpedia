-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux18_pgf_factorial_remainder
-- name    : AvramDividend.Classical.avram_redux18_pgf_factorial_remainder
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:22:10.176432+00:00
-- url     : https://prove2.me/theorems/608d0961-2ba0-4784-bbb5-85543a1c39e3
-- title:
--   Second factorial-moment remainder for an integer count PGF
-- statement:
--   For any 0≤z≤1 and integer count n, the gap between z^n and its first-order expansion 1-(1-z)n is nonnegative and bounded by half the second falling-factorial n(n−1) times (1−z)². This sharp finite-count inequality allows the exact original Lévy first and second factorial count moments to bound its small-time PGF error by O(t²), permitting a direct independent-time-cell Poisson limit.
-- source:
--   Proved by finite induction; the nth error obeys the exact recurrence Δ(n+1)=zΔ(n)+(1−z)²n. Its nonnegative and upper bounds follow from the inductive upper bound and 0≤z≤1. The original-process second factorial moment is already Proved as 0a13392f-85cb-4eda-8293-758dc8d8a2a7.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_redux18_pgf_factorial_remainder
    (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (n : ℕ) :
    0 ≤ z ^ n - (1 - (1 - z) * (n : ℝ)) ∧
    2 * (z ^ n - (1 - (1 - z) * (n : ℝ))) ≤
      (1 - z) ^ 2 * (n : ℝ) * ((n : ℝ) - 1) := by sorry
