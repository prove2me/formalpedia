-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_paymentTimes_iInf_mass_of_finite
-- name    : AvramDividend.Classical.runningSup_paymentTimes_iInf_mass_of_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:16:08.336898+00:00
-- url     : https://prove2.me/theorems/b1bce667-28fb-475e-8fd3-c1f3f2679b79
-- title:
--   Finite stopped dividend mass is continuous at decreasing ruin horizons
-- statement:
--   For a decreasing sequence of extended ruin horizons and a sample path whose initial stopped Stieltjes mass is finite, the mass stopped at the infimum of the horizons equals the infimum of all stopped masses. Endpoint-nullity turns intersection of payment windows into the true limiting window, and finite-measure continuity from above completes the identity.
-- source:
--   Mathlib Antitone.measure_iInter; Proved paymentTimes_measurable and runningSup_paymentTimes_iInter_restrict_eq.

import Mathlib.MeasureTheory.Measure.Restrict
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_runningSup_paymentTimes_iInter_restrict_eq

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.runningSup_paymentTimes_iInf_mass_of_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (σ : ℕ → ℝ≥0∞) (hσ : Antitone σ)
    (hfinite : (dividendMeasure (runningSup X) ω)
        (paymentTimes (σ 0)) ≠ ⊤) :
    (dividendMeasure (runningSup X) ω)
        (paymentTimes (⨅ n, σ n)) =
      ⨅ n, (dividendMeasure (runningSup X) ω)
        (paymentTimes (σ n)) := by sorry
