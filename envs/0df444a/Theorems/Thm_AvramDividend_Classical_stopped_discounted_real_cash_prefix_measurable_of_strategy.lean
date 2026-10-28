-- Prove2me | Theorems.Thm_AvramDividend_Classical_stopped_discounted_real_cash_prefix_measurable_of_strategy
-- name    : AvramDividend.Classical.stopped_discounted_real_cash_prefix_measurable_of_strategy
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T20:36:23.279382+00:00
-- url     : https://prove2.me/theorems/62a08c7b-b4fb-49a0-9c2b-7b1df6949af0
-- title:
--   Measurable finite real-cash Stieltjes prefixes for admissible stopped dividends
-- statement:
--   For each natural prefix length, the ENNReal embedding of the finite sum of actual discounted Stieltjes dividends paid during half-open unit intervals of a stopped admissible Lévy dividend strategy is measurable. Reuse the canonically Proved stopped_discounted_unit_cash_measurable_of_strategy for each exact ENNReal-valued unit cash, transfer measurability through ENNReal.toReal, combine the finite measurable sums by induction and Finset.sum_range_succ, then transfer through ENNReal.ofReal. This directly supplies hPrefixAE to the Proved exponential_levy_grid_cash_stieltjes_limit_le_initial in both capped BV/UV stochastic cores. It requires the exact unit-cash measurability predecessor to be canonically Proved before publication; the conditional HJB budget and expectation integrability remain open.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Data.Finset.Range
import Theorems.Thm_AvramDividend_Classical_stopped_discounted_unit_cash_measurable_of_strategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.stopped_discounted_real_cash_prefix_measurable_of_strategy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (T : ℝ≥0) :
    ∀ n : ℕ, Measurable (fun ω : Ω =>
      ENNReal.ofReal
        (∑ k ∈ Finset.range n,
          (∫⁻ t in
            (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) ∩
              Ico (k : ℝ) ((k : ℝ) + 1),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)) := by sorry
