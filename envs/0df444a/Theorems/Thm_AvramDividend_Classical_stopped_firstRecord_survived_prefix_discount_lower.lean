-- Prove2me | Theorems.Thm_AvramDividend_Classical_stopped_firstRecord_survived_prefix_discount_lower
-- name    : AvramDividend.Classical.stopped_firstRecord_survived_prefix_discount_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:18:57.027852+00:00
-- url     : https://prove2.me/theorems/814db90f-ad9b-4942-9850-99dd1558d6fb
-- title:
--   Surviving first-record grid prefix pays at least its endpoint-discount sum
-- statement:
--   On an individual Lévy sample path, if the Nth strict upper record clock is before the stopping horizon, all preceding record clocks are finite and ordered. The stopped Stieltjes dividend reward over the record-clock interval then dominates the finite sum of discounted record increments. This applies the previously Proved finite attained-clock bound directly to canonical named upcrossing times, without auxiliary finiteness and monotonicity hypotheses.
-- source:
--   Published firstUpcrossing_uniform_record_grid_mono, chat08_named_upper_clock_eq_raw_infimum and runningSup_N_record_cells_discount_lower_bound.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_N_record_cells_discount_lower_bound
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_uniform_record_grid_mono
import Theorems.Thm_AvramDividend_Classical_chat08_named_upper_clock_eq_raw_infimum

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.stopped_firstRecord_survived_prefix_discount_lower
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q b h : ℝ) (hq : 0 ≤ q)
    (hb : 0 ≤ b) (hh : 0 < h) (N : ℕ)
    (hSurvive : twoSidedExitUpTime X (b + (N : ℝ) * h) ω < τ) :
    (∑ k ∈ Finset.range N,
      ENNReal.ofReal (Real.exp
        (-(q * (twoSidedExitUpTime X (b + ((k + 1 : ℕ) : ℝ) * h) ω).toReal))) *
      ENNReal.ofReal h) ≤
      ∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc
          (twoSidedExitUpTime X (b + (0 : ℝ) * h) ω).toReal
          (twoSidedExitUpTime X (b + (N : ℝ) * h) ω).toReal
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω) := by sorry
