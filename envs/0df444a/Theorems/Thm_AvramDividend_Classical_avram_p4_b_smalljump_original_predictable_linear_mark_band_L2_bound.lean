-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_linear_mark_band_L2_bound
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_predictable_linear_mark_band_L2_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:03:08.741315+00:00
-- url     : https://prove2.me/theorems/d4f0f23a-8b07-416e-985d-690c9bd6e022
-- title:
--   Original predictable linear small-jump integrand has a quantitative L2 energy bound on every square-integrable source mark band
-- statement:
--   For the actual spectrally negative Levy process X and its right-continuous predictable sigma algebra, an arbitrary predictable bounded coefficient g has quadratic compensator energy over any Borel mark band bounded by mu(univ) M² times the genuine X.nu second moment of the band. This furnishes quantitative source-based bounds for thinning and approximation. It asserts no stochastic jump-measure martingale/isometry.
-- source:
--   Original X.nu square moment, predictable coefficient and nonnegative integral monotonicity, cf accepted source helper aa3744ce.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_predictable_linear_mark_band_L2_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (g : ℝ≥0 × Ω → ℝ)
    (hgm : Measurable[𝓕.rightCont.predictable] g)
    (M : ℝ) (hM : 0 ≤ M) (hg : ∀ p, |g p| ≤ M)
    (B : Set ℝ)
    (hBmom : (∫⁻ z in B, ENNReal.ofReal (z^2) ∂X.ν) < ⊤) :
    (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B, ENNReal.ofReal ((g p * z)^2) ∂X.ν ∂μ) ≤ μ Set.univ * (ENNReal.ofReal (M^2) * (∫⁻ z in B, ENNReal.ofReal (z^2) ∂X.ν)) ∧
    (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B, ENNReal.ofReal ((g p * z)^2) ∂X.ν ∂μ) < ⊤ := by sorry
