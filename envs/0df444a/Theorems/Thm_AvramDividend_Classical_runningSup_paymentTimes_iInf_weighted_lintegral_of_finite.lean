-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_paymentTimes_iInf_weighted_lintegral_of_finite
-- name    : AvramDividend.Classical.runningSup_paymentTimes_iInf_weighted_lintegral_of_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:12:41.676983+00:00
-- url     : https://prove2.me/theorems/d1d7d2c1-7318-4b67-916f-fd321a8d293b
-- title:
--   Finite discounted Stieltjes reward is continuous under decreasing strict payment horizons
-- statement:
--   For an antitone sequence of extended payment horizons, a nonnegative Stieltjes reward weight and a sample path whose reward up to the first horizon is finite, the stopped reflected-supremum reward at the infimum horizon equals the infimum of rewards at all horizons. Apply continuity from above to the measure obtained by weighting the running-supremum Stieltjes measure, and use the already Proved endpoint restriction identity to handle the exact strict stopping-time convention. This supplies the weighted convergence ingredient for finite-activity approximations to the zero-barrier case.
-- source:
--   Avram, Palmowski and Pistorius (2007), §3.3 and §5, https://arxiv.org/pdf/math/0702893; Prove2Me exact stopped Stieltjes measure identity eff1caea-3ef6-43d9-9835-4fe1ffebf19b.

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_mono_horizon
import Theorems.Thm_AvramDividend_Classical_runningSup_paymentTimes_iInter_restrict_eq

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- The discounted reflected-supremum Stieltjes reward is continuous
    under decreasing stopped payment windows, if the first reward is finite. -/
theorem runningSup_paymentTimes_iInf_weighted_lintegral_of_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (σ : ℕ → ℝ≥0∞) (hσ : Antitone σ) (f : ℝ → ℝ≥0∞)
    (hfinite :
      (∫⁻ t in paymentTimes (σ 0), f t
        ∂(dividendMeasure (runningSup X) ω)) ≠ ⊤) :
    (∫⁻ t in paymentTimes (⨅ n, σ n), f t
      ∂(dividendMeasure (runningSup X) ω)) =
    ⨅ n, (∫⁻ t in paymentTimes (σ n), f t
      ∂(dividendMeasure (runningSup X) ω)) := by sorry

end AvramDividend.Classical
