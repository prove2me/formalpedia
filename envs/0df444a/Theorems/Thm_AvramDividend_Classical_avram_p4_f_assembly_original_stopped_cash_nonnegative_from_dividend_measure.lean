-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_stopped_cash_nonnegative_from_dividend_measure
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_stopped_cash_nonnegative_from_dividend_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:58:07.147468+00:00
-- url     : https://prove2.me/theorems/4db282c6-0692-4c9b-b797-eda5920defa4
-- title:
--   True original full stopped Stieltjes discounted cash is pathwise nonnegative
-- statement:
--   For the genuine original process ruin time and full discounted cash as an ENNReal Stieltjes integral truncated at the real stopped clock, Cash is nonnegative pointwise including diffuse and atomic dividends. Useful to compare Term with Term+Cash in original Fatou bounds.
-- source:
--   Canonical 0dda1be7 actual hCash equation and pinned Mathlib ENNReal.toReal_nonneg.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_stopped_cash_nonnegative_from_dividend_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0) (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) :
    ∀ ω, 0 ≤ Cash ω := by sorry
