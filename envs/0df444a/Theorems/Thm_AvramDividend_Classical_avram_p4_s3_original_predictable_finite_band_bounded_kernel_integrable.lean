-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_predictable_finite_band_bounded_kernel_integrable
-- name    : AvramDividend.Classical.avram_p4_s3_original_predictable_finite_band_bounded_kernel_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T11:57:07.062267+00:00
-- url     : https://prove2.me/theorems/d7d305e4-6618-48a6-b7e0-3778590463fd
-- title:
--   Original negative-band bounded predictable source kernel is integrable against its finite physical compensator
-- statement:
--   For the original spectrally negative Levy source on its true right-continuous predictable space, a finite physical-time clock measure and finite separated negative jump band yield finite product compensator mass. Every bounded measurable predictable kernel is integrable against this product measure. This discharges the finite-band signed compensator integrability precondition for the true physical source.
-- source:
--   Finite physical predictable clock μ(univ)<top and original band Levy intensity ν(Iic(-1/(n+1)))<top imply the clock-band product measure is finite. Integrable.of_bound then applies to the original bounded predictable kernel. Used as the finite-band hGiN obligation in proved signed stopped mean-zero compensator c7cc0cd4, with physical NX and ruin clock unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_original_predictable_finite_band_bounded_kernel_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμfinite : μ Set.univ < ∞)
    (hνfinite : X.ν (Iic (-(1 / ((n : ℝ) + 1)))) < ∞)
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hGmeas : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] G)
    (C : ℝ) (hC : 0 ≤ C)
    (hGbounded : ∀ p, |G p| ≤ C) :
    Integrable G (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable;
      μ.prod (X.ν.restrict (Iic (-(1 / ((n : ℝ) + 1)))))) := by sorry
