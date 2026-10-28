-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_drift_prefix_discounted_stieltjes_eq_scaled_volume
-- name    : AvramDividend.Classical.runningSup_drift_prefix_discounted_stieltjes_eq_scaled_volume
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:54:10.753988+00:00
-- url     : https://prove2.me/theorems/39b7ea39-fb6d-4208-8e3a-2c4e1cca3edb
-- title:
--   Every discounted Stieltjes reward on a linear running-supremum prefix equals its drift-weighted Lebesgue integral
-- statement:
--   If the actual running supremum of a spectrally negative Levy process follows a nonnegative drift line through a time horizon T, then, on the dividend-payment window (0,T], its Stieltjes dividend measure agrees with the drift-scaled Lebesgue measure for every nonnegative reward weight. In particular this applies to exponential discounting before the first negative jump.
-- source:
--   Avram, Palmowski and Pistorius (2007), Section 3.3, zero-barrier first-jump payout formula.

import Theorems.Thm_AvramDividend_Classical_measure_restrict_Ioc_eq_of_local_Ioc_agreement
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_drift_before_time
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.runningSup_drift_prefix_discounted_stieltjes_eq_scaled_volume
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ)
    (hT : 0 ≤ T)
    (hPath : ∀ u : ℝ, 0 ≤ u → u ≤ T →
      runningSup X u.toNNReal ω = X.drift * u)
    (hDrift : 0 ≤ X.drift)
    (f : ℝ → ℝ≥0∞) :
    (∫⁻ t in Ioc (0 : ℝ) T, f t ∂(dividendMeasure (runningSup X) ω)) =
    (∫⁻ t in Ioc (0 : ℝ) T, f t ∂((ENNReal.ofReal X.drift) • volume)) := by sorry
