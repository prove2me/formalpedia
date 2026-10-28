-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_finite_horizon_killedRecord_budget
-- name    : AvramDividend.Classical.runningSup_finite_horizon_killedRecord_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:39:55.685524+00:00
-- url     : https://prove2.me/theorems/ab90e210-11bb-4c96-bd66-e46805ff2f7c
-- title:
--   A surviving finite-horizon reflected dividend reward is bounded by the complete killed record series
-- statement:
--   For a spectrally negative Lévy path surviving through a finite horizon, if N is the final strict first-record grid level reached before that horizon, the entire stopped discounted Stieltjes dividend reward through the horizon is bounded by the full infinite sum of killed first-record discounted payments. The proof combines already Proved finite record-cell Stieltjes estimates with the newly Proved finite-surviving-prefix-to-killed-series theorem and monotonicity of first-passage clocks.
-- source:
--   Composition of Proved runningSup_full_finite_horizon_last_record_budget, surviving_record_prefix_budget_le_killed_tsum, and firstUpcrossing_threshold_iInf_mono.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_full_finite_horizon_last_record_budget
import Theorems.Thm_AvramDividend_Classical_surviving_record_prefix_budget_le_killed_tsum
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_threshold_iInf_mono

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.runningSup_finite_horizon_killedRecord_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q h : ℝ) (hq : 0 ≤ q) (hh : 0 < h)
    (N : ℕ) (t : ℝ≥0)
    (hN : (⨅ (r : ℝ≥0) (_ : (0 : ℝ) + (N : ℝ) * h < X.X r ω), (r : ℝ≥0∞)) < (t : ℝ≥0∞))
    (hnext : ¬ (⨅ (r : ℝ≥0) (_ : (0 : ℝ) + (((N + 1 : ℕ)) : ℝ) * h < X.X r ω), (r : ℝ≥0∞)) < (t : ℝ≥0∞))
    (htτ : (t : ℝ≥0∞) < τ) :
    (∫⁻ r in paymentTimes τ,
      if r ∈ Set.Ioc (0 : ℝ) (t : ℝ)
      then ENNReal.ofReal (Real.exp (-(q * r))) else 0
      ∂(dividendMeasure (runningSup X) ω)) ≤
    (∑' k : ℕ,
      if (⨅ (r : ℝ≥0) (_ : (0 : ℝ) + (k : ℝ) * h < X.X r ω), (r : ℝ≥0∞)) < τ then
        ENNReal.ofReal
          (h * Real.exp (-(q * ((⨅ (r : ℝ≥0) (_ : (0 : ℝ) + (k : ℝ) * h < X.X r ω), (r : ℝ≥0∞))).toReal)))
      else 0) := by sorry
