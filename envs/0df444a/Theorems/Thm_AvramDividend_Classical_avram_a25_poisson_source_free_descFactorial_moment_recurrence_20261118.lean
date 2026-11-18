-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_poisson_source_free_descFactorial_moment_recurrence_20261118
-- name    : AvramDividend.Classical.avram_a25_poisson_source_free_descFactorial_moment_recurrence_20261118
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T00:25:11.924664+00:00
-- url     : https://prove2.me/theorems/5b3d8429-cdc4-4c6c-93fe-24018392b1db
-- title:
--   Exact Poisson falling-factorial integral recurrence for every order
-- statement:
--   For any nonnegative rate r and any natural order n, the (n+1)st descending factorial moment of a Poisson(r) natural-valued count equals r multiplied by its nth descending factorial moment. This is a pure discrete Poisson distribution identity independent of any Lévy process. Once proved, it transfers directly to the actual original physical negative Borel jump count using its previously established Poisson law.
-- source:
--   Pinned Mathlib ProbabilityTheory.integral_poissonMeasure, poissonMeasure singleton mass formula, Nat.descFactorial recurrence and summation shift.

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Nat
noncomputable section

theorem AvramDividend.Classical.avram_a25_poisson_source_free_descFactorial_moment_recurrence_20261118
    (r : ℝ≥0) (n : ℕ) :
    (∫ k : ℕ, (Nat.descFactorial k (n + 1) : ℝ) ∂poissonMeasure r) =
      (r : ℝ) *
        (∫ k : ℕ, (Nat.descFactorial k n : ℝ) ∂poissonMeasure r) := by sorry
