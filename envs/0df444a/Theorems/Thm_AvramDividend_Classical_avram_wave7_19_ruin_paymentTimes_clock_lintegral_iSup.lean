-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_ruin_paymentTimes_clock_lintegral_iSup
-- name    : AvramDividend.Classical.avram_wave7_19_ruin_paymentTimes_clock_lintegral_iSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T13:06:24.481058+00:00
-- url     : https://prove2.me/theorems/4242c881-1fbc-4cfd-bf4c-294673e740cf
-- title:
--   Pathwise original Stieltjes cash on full pre-ruin payment domain is supremum of integer-clock cash
-- statement:
--   For a fixed original Lévy sample path, the discounted complete Stieltjes dividend integral on the source paymentTimes(ruinTime) through T is the monotone supremum of corresponding integer-ruin-clock integrals. The time-zero payment survives and the positive-ruin-time boundary remains excluded. This removes the pathwise hLimit hypothesis in W7-19's outer MCT bridge without stochastic assumptions.
-- source:
--   Original dividendMeasure, paymentTimes and ruinTime definitions; follows from Proved W7-19 clock-set union cfd0e11a and pinned Mathlib lintegral_iSup for measurable indicator functions over increasing Borel source payment sets.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_ruin_paymentTimes_clock_lintegral_iSup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) = ⨆ n : ℕ, (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
