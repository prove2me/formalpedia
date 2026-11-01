-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_stopped_fullStieltjes_realDiscount_payoff_le_expCapital
-- name    : AvramDividend.Classical.avram_wave4_03_original_stopped_fullStieltjes_realDiscount_payoff_le_expCapital
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:12:15.290286+00:00
-- url     : https://prove2.me/theorems/3cf94f6f-64fe-4d45-846b-9aefdf8a0cab
-- title:
--   True original source stopped full Stieltjes real-clock discounted dividend payoff bounded by exp(initial capital)
-- statement:
--   For an actual capped admissible left-continuous right-payment control D on the same probability space and filtration as the original spectrally negative Lévy X, the expected entire strictly pre-ruin dividendMeasure cash on paymentTimes(ruinTime) intersected with the real-clock horizon Iic T is bounded above by exp x at discount ψ(1). This exactly matches the real-time stopped payoff convention of the canonical verification, including the time-zero right payment, all positive-time atoms and diffuse and singular-continuous Stieltjes mass. It follows from the full Icc expected stopped exponential source budget and the corrected chronological reward restriction bridge; this is only the exponential-test case, not general C1 HJB verification.
-- source:
--   Full closed-horizon original stopped exponential budget target (currently Open at draft time), and proved Chat04B stopped original reward restriction 122d4c4b-f0ad-47c3-a555-9ddfc26bd6d8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_source_closedHorizon_stopped_fullStieltjes_exponential_verification
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_stopped_original_reward_eq_closed_horizon_restriction
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.avram_wave4_03_original_stopped_fullStieltjes_realDiscount_payoff_le_expCapital
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(X.ψ 1 * s)))
        ∂dividendMeasure D ω ∂P) ≤ ENNReal.ofReal (Real.exp x) := by sorry
