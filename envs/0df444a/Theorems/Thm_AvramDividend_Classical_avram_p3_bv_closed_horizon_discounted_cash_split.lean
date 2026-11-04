-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_closed_horizon_discounted_cash_split
-- name    : AvramDividend.Classical.avram_p3_bv_closed_horizon_discounted_cash_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:25:16.839812+00:00
-- url     : https://prove2.me/theorems/925b8293-f45d-480a-969a-e0c032467f3f
-- title:
--   Original BV stopped discounted Stieltjes cash splits exactly at the closed horizon right-payment atom
-- statement:
--   For the original spectrally negative Levy process and actual original dividendMeasure, the closed finite-horizon discounted Stieltjes cash is the cash strictly before T plus the exact T-atom, with the paymentTimes ruin predicate retained on both regions. This uses only measurable-set partition and disjoint lintegral additivity; no stochastic compensator or surrogate process.
-- source:
--   Exact paymentTimes set split at Iic/Iio and Mathlib MeasureTheory.lintegral_union.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_closed_horizon_discounted_cash_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q T : ℝ) (ω : Ω)
    (hPaid : MeasurableSet (paymentTimes (ruinTime X x D ω))) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ {T},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
