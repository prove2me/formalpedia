-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_discounted_interval_weight_bounds
-- name    : AvramDividend.Classical.runningSup_discounted_interval_weight_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T13:24:08.04855+00:00
-- url     : https://prove2.me/theorems/6eb26a81-d7b8-4a3f-bf99-da311680c70c
-- title:
--   Lower and upper discount-weight bounds for genuine running-supremum dividend Stieltjes increments
-- statement:
--   Fix a Lévy sample path, its running-supremum dividend measure, a half-open time interval (s,t], and an antitone nonnegative payment discount w. The discounted dividend integral over the interval is between the integral of the constant terminal discount w(t) and the integral of the constant initial discount w(s), with each integral zero outside (s,t]. This pathwise-in-measure result is valid for arbitrary s and t, including an empty interval, and is the rigorous first step in bounding stopped Stieltjes dividend sums by geometric discounted new-record weights. The theorem assumes only antitonicity of w and does not claim any renewal equality.
-- source:
--   Mathlib lintegral_mono applied to the actual running-supremum dividend measure; Avram Palmowski Pistorius 2007 Section 3.3 discounted dividend record integrals.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_discounted_interval_weight_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (w : ℝ → ℝ≥0∞) (hw : Antitone w)
    (s t : ℝ) :
    ((∫⁻ r, if r ∈ Set.Ioc s t then w t else 0
         ∂(dividendMeasure (runningSup X) ω)) ≤
     (∫⁻ r, if r ∈ Set.Ioc s t then w r else 0
         ∂(dividendMeasure (runningSup X) ω))) ∧
    ((∫⁻ r, if r ∈ Set.Ioc s t then w r else 0
         ∂(dividendMeasure (runningSup X) ω)) ≤
     (∫⁻ r, if r ∈ Set.Ioc s t then w s else 0
         ∂(dividendMeasure (runningSup X) ω))) := by sorry
