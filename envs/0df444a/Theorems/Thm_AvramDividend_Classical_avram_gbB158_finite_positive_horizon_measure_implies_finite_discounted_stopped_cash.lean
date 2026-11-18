-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB158_finite_positive_horizon_measure_implies_finite_discounted_stopped_cash
-- name    : AvramDividend.Classical.avram_gbB158_finite_positive_horizon_measure_implies_finite_discounted_stopped_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:18:52.445022+00:00
-- url     : https://prove2.me/theorems/66b7da01-81f9-4351-8796-fc85d623b9b3
-- title:
--   Finite measure on nonnegative physical horizon makes every strictly stopped discounted cash integral finite
-- statement:
--   For an arbitrary measure on real payment times, q≥0, a finite horizon T≥0 and any measurable cash region contained within [0,T], finite measure of [0,T] guarantees the nonnegative discounted cash integral over that region is finite. This is a generic source-compatible finiteness certificate; applied to the genuine original dividendMeasure, it can discharge the finite-cash assumption in the strict stopped Gaussian counterexample once the original barrier measure mass bound is supplied.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB158_finite_positive_horizon_measure_implies_finite_discounted_stopped_cash
    (μ : Measure ℝ) (q T : ℝ)
    (hq : 0 ≤ q) (hT : 0 ≤ T)
    (A : Set ℝ) (hA : A ⊆ Icc (0 : ℝ) T)
    (hMass : μ (Icc (0 : ℝ) T) ≠ ⊤) :
    (∫⁻ t in A,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) ≠ ⊤ := by sorry
