-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_finite_band_compensated_variance_of_raw_moments
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_finite_band_compensated_variance_of_raw_moments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:56:45.749871+00:00
-- url     : https://prove2.me/theorems/4aad78f4-17d0-41e4-8264-0415381fbf46
-- title:
--   Original intrinsic marked finite-band count compensated variance from its raw moments
-- statement:
--   The original process marked-jump count with first moment r and second moment r squared plus r has expected squared centered count equal r under its physical probability measure, reducing finite-band L2 isometry to proving source law moments.
-- source:
--   Exact original SpectrallyNegativeLevy X.X intrinsic marked jump counts and pinned Mathlib real Bochner integral linearity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_finite_band_compensated_variance_of_raw_moments
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : Set ℝ) (J : Ω → ℝ)
    (hSource : ∀ ω, J ω =
      (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal)
    (hJ : Integrable J P)
    (hJ2 : Integrable (fun ω => (J ω) ^ 2) P)
    (r : ℝ) (hRate : r =
      ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal)
    (hFirst : (∫ ω, J ω ∂P) = r)
    (hSecond : (∫ ω, (J ω) ^ 2 ∂P) = r ^ 2 + r) :
    (∫ ω, (J ω - r) ^ 2 ∂P) = r := by sorry
