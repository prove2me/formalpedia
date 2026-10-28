-- Prove2me | Theorems.Thm_AvramDividend_Classical_stopped_lintegral_zero_through_extended_first_record
-- name    : AvramDividend.Classical.stopped_lintegral_zero_through_extended_first_record
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:28:35.691243+00:00
-- url     : https://prove2.me/theorems/497d0897-898a-489e-a771-5b06ecce0e02
-- title:
--   Zero stopped dividends whenever the finite horizon reaches no positive record
-- statement:
--   For every finite observation horizon t no later than the extended first strict positive upcrossing clock, the stopped weighted running-supremum Stieltjes integral over (0,t] vanishes. This includes equality at a finite first clock and the case of an infinite first clock, and directly discharges the no-record branch of the stopped-renewal pathwise upper-bound argument.
-- source:
--   Lift the proved zero Stieltjes measure on the interval through the extended first positive record to the payment-time-restricted measure and apply lintegral_eq_zero_of_ae.

import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_up_to_extended_first_positive_record

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.stopped_lintegral_zero_through_extended_first_record
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (f : ℝ → ℝ≥0∞) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) ≤
      (⨅ (r : ℝ≥0) (_ : (0 : ℝ) < X.X r ω), (r : ℝ≥0∞))) :
    (∫⁻ r in paymentTimes τ,
      if r ∈ Set.Ioc (0 : ℝ) (t : ℝ) then f r else 0
      ∂(dividendMeasure (runningSup X) ω)) = 0 := by sorry
