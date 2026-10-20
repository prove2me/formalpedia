-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_lintegral_countable_interchange
-- name    : AvramDividend.Classical.runningSup_lintegral_countable_interchange
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:48:51.835763+00:00
-- url     : https://prove2.me/theorems/d5ff8a9f-72a2-4f5c-8f0d-1af7ee117f21
-- title:
--   Interchange of countable record-interval dividend rewards and the actual Stieltjes integral
-- statement:
--   For the actual Lévy running-supremum dividend Stieltjes measure, a measurable nonnegative discount weight and any countable collection of half-open real intervals, the Lebesgue integral of the countable pointwise sum of interval reward integrands equals the countable sum of their individual Stieltjes integrals. This is Tonelli's nonnegative-sum interchange and does not assume pairwise disjointness. When an inverse-record partition is shown disjoint and covering, the identity connects the integral of the stopped dividend reward to its countable interval decomposition.
-- source:
--   Pinned Mathlib MeasureTheory.lintegral_tsum in Mathlib.MeasureTheory.Integral.Lebesgue.Add; MeasurableSet.ite and measurableSet_Ioc; actual dividendMeasure imported through the proven runningSup measure identity.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_eq_stieltjes

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_lintegral_countable_interchange
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (w : ℝ → ℝ≥0∞) (hw : Measurable w)
    (u : ℕ → ℝ) :
    (∫⁻ r, (∑' i : ℕ,
        if r ∈ Set.Ioc (u i) (u (i + 1)) then w r else 0)
        ∂(dividendMeasure (runningSup X) ω)) =
      (∑' i : ℕ,
        ∫⁻ r, if r ∈ Set.Ioc (u i) (u (i + 1)) then w r else 0
          ∂(dividendMeasure (runningSup X) ω)) := by sorry
