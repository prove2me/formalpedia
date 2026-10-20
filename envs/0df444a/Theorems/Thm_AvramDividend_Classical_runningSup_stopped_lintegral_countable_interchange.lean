-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_stopped_lintegral_countable_interchange
-- name    : AvramDividend.Classical.runningSup_stopped_lintegral_countable_interchange
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T21:16:06.344934+00:00
-- url     : https://prove2.me/theorems/03617d3a-5808-4b94-a0c4-4381b6d0d721
-- title:
--   Tonelli interchange for actual Stieltjes dividends restricted to the original stopped payment times
-- statement:
--   For the actual running-supremum Stieltjes dividend measure restricted to the original paymentTimes of an arbitrary extended-nonnegative stopping horizon, the integral of any countable sum of interval-weighted measurable dividend payoffs equals the sum of the stopped interval integrals. This is the stopped version of nonnegative Tonelli interchange; it explicitly retains the original time-zero payment convention and applies without assuming the strict reflected ruin time is positive.
-- source:
--   Pinned Mathlib MeasureTheory.lintegral_tsum exact remote signature confirmed; accepted runningSup_lintegral_countable_interchange target d5ff8a9f-72a2-4f5c-8f0d-1af7ee117f21; actual paymentTimes in Definitions.Def_AvramDividend_Classical_ReflectionBarrier.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_stopped_lintegral_countable_interchange
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (w : ℝ → ℝ≥0∞) (hw : Measurable w)
    (u : ℕ → ℝ) :
    (∫⁻ r in paymentTimes τ,
      (∑' i : ℕ,
        if r ∈ Set.Ioc (u i) (u (i + 1)) then w r else 0)
        ∂(dividendMeasure (runningSup X) ω)) =
    (∑' i : ℕ,
       ∫⁻ r in paymentTimes τ,
         if r ∈ Set.Ioc (u i) (u (i + 1)) then w r else 0
         ∂(dividendMeasure (runningSup X) ω)) := by sorry
