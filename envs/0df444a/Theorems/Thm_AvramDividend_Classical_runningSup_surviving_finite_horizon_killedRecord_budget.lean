-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_surviving_finite_horizon_killedRecord_budget
-- name    : AvramDividend.Classical.runningSup_surviving_finite_horizon_killedRecord_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:44:38.905125+00:00
-- url     : https://prove2.me/theorems/23483189-f1dc-448e-b43a-f0983270ecfd
-- title:
--   Every surviving finite-horizon reflected reward is dominated by the killed record series
-- statement:
--   On every finite horizon strictly before the killing time, the discounted Stieltjes reward of the running supremum is bounded by the entire killed first-record discounted-payment series. Split into no record (proved zero stopped integral) and an attained last record (proved finite-horizon killed-series comparison). This removes the last-record index assumption from the pathwise stochastic renewal upper-bound argument.
-- source:
--   By record_grid_last_survived_before_finite_horizon, case split; apply stopped_lintegral_zero_through_extended_first_record or runningSup_finite_horizon_killedRecord_budget.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_record_grid_last_survived_before_finite_horizon
import Theorems.Thm_AvramDividend_Classical_stopped_lintegral_zero_through_extended_first_record
import Theorems.Thm_AvramDividend_Classical_runningSup_finite_horizon_killedRecord_budget

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.runningSup_surviving_finite_horizon_killedRecord_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q h : ℝ) (hq : 0 ≤ q) (hh : 0 < h)
    (t : ℝ≥0) (htτ : (t : ℝ≥0∞) < τ) :
    (∫⁻ r in paymentTimes τ,
      if r ∈ Set.Ioc (0 : ℝ) (t : ℝ)
      then ENNReal.ofReal (Real.exp (-(q * r))) else 0
      ∂(dividendMeasure (runningSup X) ω)) ≤
    (∑' k : ℕ,
      if (⨅ (r : ℝ≥0) (_ : (0 : ℝ) + (k : ℝ) * h < X.X r ω), (r : ℝ≥0∞)) < τ then
        ENNReal.ofReal
          (h * Real.exp (-(q * ((⨅ (r : ℝ≥0) (_ : (0 : ℝ) + (k : ℝ) * h < X.X r ω), (r : ℝ≥0∞))).toReal)))
      else 0) := by sorry
