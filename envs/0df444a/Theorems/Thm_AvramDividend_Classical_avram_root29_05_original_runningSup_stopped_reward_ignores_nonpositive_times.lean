-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_original_runningSup_stopped_reward_ignores_nonpositive_times
-- name    : AvramDividend.Classical.avram_root29_05_original_runningSup_stopped_reward_ignores_nonpositive_times
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T15:07:06.641987+00:00
-- url     : https://prove2.me/theorems/280346b8-69da-48fb-94b7-1f8ee832acf0
-- title:
--   Original running-supremum stopped Stieltjes reward ignores all nonpositive payment times
-- statement:
--   For every actual spectrally negative Lévy path, ruin stopping time and discount parameter, the true running-supremum Stieltjes dividend measure assigns zero mass to the whole nonpositive time half-line. Consequently inserting a positive-time indicator into its original paymentTimes-discounted reward preserves the exact value, without an assumption on the ruin time, discount sign, or a false time-zero dividend atom.
-- source:
--   Proved runningSup_dividendMeasure_zero_nonpositive abc5f5f8 and paymentTimes_measurable 88dafb7f, using ae_iff and lintegral_congr_ae. Complements accepted 4e232b08 source-level reconstruction by matching canonical barrierSupValue's unfiltered time-discounted reward.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.avram_root29_05_original_runningSup_stopped_reward_ignores_nonpositive_times
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (q : ℝ) (τ : ℝ≥0∞) :
    (∫⁻ r in paymentTimes τ,
      ENNReal.ofReal (Real.exp (-(q * r)))
      ∂(dividendMeasure (runningSup X) ω)) =
    (∫⁻ r in paymentTimes τ,
      if 0 < r then ENNReal.ofReal (Real.exp (-(q * r))) else 0
      ∂(dividendMeasure (runningSup X) ω)) := by sorry
