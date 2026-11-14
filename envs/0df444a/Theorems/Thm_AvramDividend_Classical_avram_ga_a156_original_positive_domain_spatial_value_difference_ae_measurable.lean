-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a156_original_positive_domain_spatial_value_difference_ae_measurable
-- name    : AvramDividend.Classical.avram_ga_a156_original_positive_domain_spatial_value_difference_ae_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:26:16.592721+00:00
-- url     : https://prove2.me/theorems/fd7ac95f-01b3-4bf9-88ab-1d5d0bdd698a
-- title:
--   Original Gaussian stopped positive-domain value difference is a.e. strongly measurable when measured endpoints are either equal or strictly positive
-- statement:
--   For the original Gaussian positive-interior source, spatial value w is smooth only on the strictly positive reserve domain, and the source stopped-cell positive observation theorem ga43 certifies an almost-sure alternative: the two source states coincide or both lie in that domain. If endpoints and discount are measurable, then the discounted value difference is a.e. strongly measurable even if w is arbitrary outside the positive domain, because a continuous positive-domain zero-extension gives a measurable representative and coincident outside-domain values cancel exactly.
-- source:
--   Pinned Mathlib ContinuousOn.measurable_piecewise and AEStronglyMeasurable.congr, source-specific Proved original stopped Gaussian cell positive-or-inactive alternative ga43.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a156_original_positive_domain_spatial_value_difference_ae_measurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ioi (0 : ℝ)))
    (Y Z E : Ω → ℝ) (hY : Measurable Y) (hZ : Measurable Z)
    (hE : Measurable E)
    (hAlt : ∀ᵐ ω ∂P, Y ω = Z ω ∨ (0 < Y ω ∧ 0 < Z ω)) :
    AEStronglyMeasurable
      (fun ω => E ω * (w (Z ω) - w (Y ω))) P := by sorry
