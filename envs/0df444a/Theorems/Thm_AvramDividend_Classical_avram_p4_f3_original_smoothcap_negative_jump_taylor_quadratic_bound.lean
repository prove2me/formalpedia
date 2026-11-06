-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_smoothcap_negative_jump_taylor_quadratic_bound
-- name    : AvramDividend.Classical.avram_p4_f3_original_smoothcap_negative_jump_taylor_quadratic_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:04:14.111394+00:00
-- url     : https://prove2.me/theorems/950c434c-5541-4b24-a3ed-4d0b64bf45e5
-- title:
--   Original smooth-cap negative-jump compensated Taylor kernel quadratic source bound
-- statement:
--   For the original spectrally negative Lévy X, its actual compensated nonlinear generatorIntegrand of the canonical C2 HJB test w has a uniformly quadratic bound over strictly-positive reserve states and genuinely small negative jump marks. Only the actual positive capped interior smoothness is assumed, including C=top; the witness a is an explicitly chosen point below the source cap. This is a localised analytic generator estimate, not a martingale identity.
-- source:
--   Restricts the exact canonical smoothness domain (positive y with ENNReal.ofReal y<C) to the physical real interval (0,a) and applies the already Proved compact original compensated generator Taylor theorem 485f09e2. The generator term is the actual source SpectrallyNegativeLevy.generatorIntegrand w u z. No changed process, fabricated first or second moments, or new hypotheses beyond explicit interior localisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_generator_integrand_uniform_near_C2_quadratic_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_smoothcap_negative_jump_taylor_quadratic_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a δ K : ℝ) (hδ : 0 < δ) (hδK : δ < K)
    (hKa : K < a) (ha : ENNReal.ofReal a < C) :
    ∃ r B : ℝ, 0 < r ∧ r ≤ min δ 1 ∧ 0 ≤ B ∧
      ∀ u ∈ Icc δ K, ∀ z ∈ Ioo (-r) 0,
        ‖SpectrallyNegativeLevy.generatorIntegrand w u z‖
          ≤ B * z ^ 2 := by sorry
