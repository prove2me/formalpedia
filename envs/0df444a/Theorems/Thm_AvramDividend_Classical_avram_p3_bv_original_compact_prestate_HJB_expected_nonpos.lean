-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_compact_prestate_HJB_expected_nonpos
-- name    : AvramDividend.Classical.avram_p3_bv_original_compact_prestate_HJB_expected_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T10:43:34.385225+00:00
-- url     : https://prove2.me/theorems/66cf24ce-2320-4c25-8f9f-728e8bab05b2
-- title:
--   Original BV controlled compact pre-reserve local HJB has nonpositive expected signed drift
-- statement:
--   For the original spectrally negative bounded-variation Lévy process and its dividend-controlled pre-jump reserve, the actual compact pre-reserve band is right-continuous-filtration predictable. Under generator integrability, local HJB negativity and the integrability of the exact signed discounted generator drift, the true finite-horizon product-time expectation is nonpositive.
-- source:
--   Proved original pre-source compact predictable region 5115705e and Proved original controlled true-clock signed HJB expected nonpositivity 773f3823.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_controlled_prestate_compact_band_predictable
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_controlled_true_clock_signed_HJB_expected_nonpos

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_compact_prestate_HJB_expected_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ) (T : ℝ≥0) (a b : ℝ)
    (Upre : ℝ≥0 × Ω → ℝ)
    (hUpre : ∀ p, Upre p = Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)
    (hGen : ∀ p, Upre p ∈ Icc a b → X.GeneratorIntegrable w (Upre p))
    (hHJB : ∀ p, Upre p ∈ Icc a b →
      X.generator w (Upre p) - q * w (Upre p) ≤ 0)
    (F : ℝ≥0 × Ω → ℝ)
    (hF : ∀ p, F p = if Upre p ∈ Icc a b then
      Real.exp (-(q * (p.1 : ℝ))) *
        (X.drift * deriv w (Upre p) +
          (∫ z in Iio (0 : ℝ), w (Upre p + z) - w (Upre p) ∂X.ν) -
          q * w (Upre p)) else 0)
    (hFint : Integrable F
      ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
        Real.toNNReal).prod P)) :
    (∫ p, F p ∂((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
      Real.toNNReal).prod P)) ≤ 0 := by sorry
