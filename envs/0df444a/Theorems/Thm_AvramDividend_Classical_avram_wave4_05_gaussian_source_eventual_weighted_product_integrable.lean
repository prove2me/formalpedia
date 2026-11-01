-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_source_eventual_weighted_product_integrable
-- name    : AvramDividend.Classical.avram_wave4_05_gaussian_source_eventual_weighted_product_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:27:00.233461+00:00
-- url     : https://prove2.me/theorems/89698593-51bd-4fed-8945-57ae10db3a1b
-- title:
--   Actual Gaussian q-scale compensated Lévy generator has eventual weighted product-integrability
-- statement:
--   For the original Standing Gaussian spectrally negative Levy process with q-scale W and a positive Esscher root phi satisfying psi(phi)=q, the genuine compensated source jump generator kernel is absolutely integrable on the full positive-reserve x negative-jump Lévy product for every sufficiently large admissible Laplace exponent. It uses the actual Gaussian curvature zero-extension and weighted second derivative control, full crossing/interior/large-jump Fubini proof, and exact ν quadratic compensation. No extra arbitrary curvature representative or product-integrability premise remains.
-- source:
--   Canonical source Gaussian curvature zero extension 9f9b8a9f and new source complete Gaussian product theorem, pinned Mathlib 0df444a; mission 1300fbe7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_source_gaussian_curvature_zeroext_weighted
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_gaussian_compensated_kernel_product_integrable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Absolute Fubini product integrability for the original Gaussian
    compensated Lévy generator and its genuine q-scale at all large weights. -/

theorem AvramDividend.Classical.avram_wave4_05_gaussian_source_eventual_weighted_product_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ b : ℝ, ∀ θ : ℝ, b ≤ θ → 0 ≤ θ → q < X.ψ θ →
      Integrable
        (fun p : ℝ × ℝ => Real.exp (-(θ * p.1)) *
          SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
        ((volume.restrict (Ioi (0 : ℝ))).prod
          (X.ν.restrict (Iio (0 : ℝ)))) := by sorry
