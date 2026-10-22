-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_adjacent_interval_integral_bound_fin
-- name    : AvramDividend.Classical.chat07_adjacent_interval_integral_bound_fin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T21:31:18.003504+00:00
-- url     : https://prove2.me/theorems/67254116-c291-4720-bcae-665a06ed621f
-- title:
--   Finite interval-sum bound from adjacent unit comparisons
-- statement:
--   Let f and g be real-valued functions interval integrable over every finite real interval and let c be real. Suppose for every natural n, the interval integral of f from n to n+1 is at most c times the interval integral of g from n+1 to n+2. Then for every natural N, the integral of f from 0 to N is at most c times the integral of g from 1 to N+1. The proof is a finite induction using additivity of interval integrals, with no positivity hypothesis or infinite-series machinery. This supports the Avram BV scale-function weighted-derivative integrability programme.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat07_adjacent_interval_integral_bound_fin
    (f g : ℝ → ℝ) (c : ℝ)
    (hf : ∀ a b : ℝ, IntervalIntegrable f volume a b)
    (hg : ∀ a b : ℝ, IntervalIntegrable g volume a b)
    (hstep : ∀ n : ℕ,
        (∫ x in (n : ℝ)..((n : ℝ) + 1), f x) ≤
          c * (∫ x in ((n : ℝ) + 1)..((n : ℝ) + 2), g x))
    (n : ℕ) :
    (∫ x in (0 : ℝ)..(n : ℝ), f x) ≤
      c * (∫ x in (1 : ℝ)..((n : ℝ) + 1), g x) := by sorry
