-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_stopped_firstRecord_step_discount_bounds
-- name    : AvramDividend.Classical.runningSup_stopped_firstRecord_step_discount_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T20:05:50.381254+00:00
-- url     : https://prove2.me/theorems/a87a10e8-a1d2-4485-a173-c0cf2d7e72d0
-- title:
--   Exact h-step bounds for stopped Stieltjes dividend payments between successive finite record upcrossings
-- statement:
--   For a genuine spectrally negative Lévy path, let u and v be finite first upward passage times of nonnegative record levels b and b+h, with h≥0. Suppose v is strictly before the selected payment horizon τ. Then the actual q-discounted Stieltjes dividend reward paid between these record times lies between h exp(-qv) and h exp(-qu), interpreted as extended-nonnegative products. Both record levels are attained without overshoot, so the original dividend measure of (u,v] has exactly h units of mass. The terminal-survival hypothesis ensures every dividend in this cell remains payable under the original stopping convention. This is the genuine record-level h-cell discretisation bridge needed before first-record killed Markov renewal and geometric reward summation.
-- source:
--   Dependency-gated runningSup_dividendMeasure_between_attained_record_levels target bb7d9d85-49b1-4aaf-a2ea-102bc6a05a2a candidate 12466; accepted runningSup_dividendMeasure_Ioc_eq_record_increment target 7343971b-047e-4925-9fa7-7ee76f6a2b23; accepted paymentTimes_Ioc_subset_of_terminal_survival target 4256f782-3b6d-4b44-adf5-367a4cc593d8; accepted runningSup_stopped_Ioc_discount_record_bounds_of_survival target 7d59aefb-31f3-40d2-85e0-b0477c351129.

import Mathlib.Data.NNReal.Defs
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_between_attained_record_levels
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_record_increment
import Theorems.Thm_AvramDividend_Classical_paymentTimes_Ioc_subset_of_terminal_survival
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_Ioc_discount_record_bounds_of_survival

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_stopped_firstRecord_step_discount_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q)
    (b h : ℝ) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (u v : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b < X.X r ω), (r : ℝ≥0∞)))
    (hv : (v : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b + h < X.X r ω), (r : ℝ≥0∞)))
    (hSurvive : ENNReal.ofReal (v : ℝ) < τ) :
    (ENNReal.ofReal (Real.exp (-(q * (v : ℝ)))) * ENNReal.ofReal h ≤
      ∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc (u : ℝ) (v : ℝ)
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ∧
    (∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc (u : ℝ) (v : ℝ)
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω) ≤
      ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) * ENNReal.ofReal h) := by sorry
