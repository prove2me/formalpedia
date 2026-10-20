-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_discounted_interval_mass_bounds
-- name    : AvramDividend.Classical.runningSup_discounted_interval_mass_bounds
-- status  : Open
-- author  : @WillR
-- created : 2026-10-19T13:42:49.572461+00:00
-- url     : https://prove2.me/theorems/8f76ca28-eaee-49ac-9ec6-53e6fd16437c
-- title:
--   Actual discounted dividend on a time interval bounded by endpoint weights times Stieltjes dividend mass
-- statement:
--   For any actual spectrally negative Lévy running-supremum dividend measure, any half-open time interval (s,t], and any antitone nonnegative weight, the weighted Stieltjes dividend integral is bounded below by w(t) times the measure of (s,t] and above by w(s) times that measure. This makes the previous pointwise-weight integral sandwich numerical via the exact measurable indicator-constant integral identity. The result is the essential input to discounted payment partition bounds, and is valid for arbitrary finite s,t including an empty interval without claiming a killed Markov renewal identity.
-- source:
--   Remotely Proved runningSup_discounted_interval_weight_bounds 6eb26a81-d7b8-4a3f-bf99-da311680c70c; pinned Mathlib MeasureTheory.lintegral_indicator_const and measurableSet_Ioc; Avram Palmowski Pistorius 2007 regulator dividend valuation.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_discounted_interval_weight_bounds

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_discounted_interval_mass_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (w : ℝ → ℝ≥0∞) (hw : Antitone w)
    (s t : ℝ) :
    (w t * (dividendMeasure (runningSup X) ω) (Set.Ioc s t) ≤
      (∫⁻ r, if r ∈ Set.Ioc s t then w r else 0
         ∂(dividendMeasure (runningSup X) ω))) ∧
    ((∫⁻ r, if r ∈ Set.Ioc s t then w r else 0
         ∂(dividendMeasure (runningSup X) ω)) ≤
      w s * (dividendMeasure (runningSup X) ω) (Set.Ioc s t)) := by sorry
