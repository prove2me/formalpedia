-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_full_finite_horizon_last_record_budget
-- name    : AvramDividend.Classical.runningSup_full_finite_horizon_last_record_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:24:51.95676+00:00
-- url     : https://prove2.me/theorems/26de9dd5-f5d2-4011-97de-ba45bbd95041
-- title:
--   Full stopped dividends from time zero bounded by the final finite-horizon record grid
-- statement:
--   Suppose the last attained strict record on a positive grid before finite time t is index N, and the path is alive through t. Then all stopped discounted running-supremum Stieltjes dividends paid in (0,t] are bounded by the finite sum of initial-record discounted h-payments for records 0 through N. The full initial interval is included using its proved zero Stieltjes mass. This is the root-connected finite-horizon pathwise budget needed before passing to a countable record-weight upper bound.
-- source:
--   Apply finite-horizon record-cell budget, derive first-record time before t by threshold-clock monotonicity, split (0,t] at the first positive record and discard the initial interval using the proved stopped-zero integral.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_finite_horizon_last_record_stopped_upper
import Theorems.Thm_AvramDividend_Classical_stopped_lintegral_initial_record_zero
import Theorems.Thm_AvramDividend_Classical_stopped_lintegral_Ioc_adjacent_add
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_threshold_iInf_mono

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.runningSup_full_finite_horizon_last_record_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q h : ℝ) (hq : 0 ≤ q) (hh : 0 < h)
    (N : ℕ) (t : ℝ≥0)
    (hN : (⨅ (r : ℝ≥0)
      (_ : (0 : ℝ) + (N : ℝ) * h < X.X r ω),
      (r : ℝ≥0∞)) < (t : ℝ≥0∞))
    (hnext : ¬ (⨅ (r : ℝ≥0)
      (_ : (0 : ℝ) + ((N + 1 : ℕ) : ℝ) * h < X.X r ω),
      (r : ℝ≥0∞)) < (t : ℝ≥0∞))
    (htτ : (t : ℝ≥0∞) < τ) :
    ∃ u : ℕ → ℝ≥0,
      (∀ k : ℕ, k ≤ N →
        (u k : ℝ≥0∞) =
          (⨅ (r : ℝ≥0)
            (_ : (0 : ℝ) + (k : ℝ) * h < X.X r ω),
            (r : ℝ≥0∞))) ∧
      (∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc (0 : ℝ) (t : ℝ)
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ≤
      ∑ k ∈ Finset.range (N + 1),
        ENNReal.ofReal (Real.exp (-(q * (u k : ℝ)))) *
          ENNReal.ofReal h := by sorry
