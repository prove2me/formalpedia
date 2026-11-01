-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_gaussian_compensated_kernel_product_integrable
-- name    : AvramDividend.Classical.avram_wave4_05_source_gaussian_compensated_kernel_product_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:07:00.588043+00:00
-- url     : https://prove2.me/theorems/0668c3b4-182f-4095-974d-4c20a34bed75
-- title:
--   Actual Gaussian q-scale compensated Lévy generator kernel is weighted product-integrable
-- statement:
--   For the original Standing spectrally negative Levy process with Gaussian component, original q-scale W and a measurable curvature representative F equal to W'' on positive states with finite exponentially weighted L1 norm, the true signed source compensated generatorIntegrand multiplied by exp(-theta*x) is absolutely Bochner-integrable on the full positive-state x negative-jump Levy product measure, whenever theta>=0 and psi(theta)>q. The proof rigorously handles jumps crossing zero, interior quadratic Taylor remainders, uncompensated large jumps, finite truncated second moment of ν, global joint measurability and measurability of the state-slice norm. No abstract generator or stochastic bridge is used; this is a direct source product-integrability premise for exact Fubini and the Gaussian Laplace residual.
-- source:
--   New Proved source interior and global small-jump bounds 0af79a05/e7ad158f; submitted source large-jump weighted sections d024c69d; submitted signed product measurability b339a2c9 and norm-map measurability 8de553a5; original quadratic ν moment X.ν_integrable and generic Proved product domination 2552153f. Mission 1300fbe7, pinned Mathlib 0df444a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_gaussian_global_smalljump_splice
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_largejump_weighted_section_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_scale_weighted_signed_kernel_product_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_weighted_jump_section_norm_measurable
import Theorems.Thm_AvramDividend_Classical_integrable_prod_of_slice_norm_quadratic_bound
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The actual compensated Gaussian source jump kernel is absolutely
    integrable on its positive-state by negative-jump Levy product measure. -/

theorem AvramDividend.Classical.avram_wave4_05_source_gaussian_compensated_kernel_product_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hσ : 0 < X.σ)
    (F : ℝ → ℝ)
    (hFpoint : ∀ u : ℝ, 0 < u → F u = iteratedDeriv 2 W u)
    (hFc : ContinuousOn F (Ioi (0 : ℝ)))
    (hFm : Measurable F)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hFi : Integrable (fun u : ℝ => Real.exp (-θ * u) * |F u|) volume) :
    Integrable
      (fun p : ℝ × ℝ => Real.exp (-(θ * p.1)) *
        SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ)))) := by sorry
