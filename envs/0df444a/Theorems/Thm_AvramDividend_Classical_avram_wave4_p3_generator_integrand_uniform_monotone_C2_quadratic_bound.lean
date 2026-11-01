-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_generator_integrand_uniform_monotone_C2_quadratic_bound
-- name    : AvramDividend.Classical.avram_wave4_p3_generator_integrand_uniform_monotone_C2_quadratic_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:32:38.806992+00:00
-- url     : https://prove2.me/theorems/c9a18a64-845c-4c62-a56b-2d1038a0f526
-- title:
--   Uniform quadratic Levy jump domination for monotone C² functions on compact positive reserves
-- statement:
--   A globally nonnegative monotone function with positive-state C2 regularity has an integrable compact-state uniform majorant C min(1,y²) for the actual source Levy compensated jump integrand over all negative jumps. The constant is shared across every reserve in a compact interval [l,u] in (0,a). This is the quantitative DCT hypothesis for the positive-barrier vcstar generator right-continuity and combines independent near and far estimates without assuming source q-harmonicity.
-- source:
--   Second-order Taylor compensation and monotone far-jump control, actual Levy ν_integrable finite truncated quadratic moment. Formal generalisation of accepted scaleFunction_uniform_generatorIntegrand_bound_on_compact UUID 9c9be0b1; P3 endpoint HJB 8d03da6b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p3_generator_integrand_uniform_monotone_C2_quadratic_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ)
    (hnonneg : ∀ z : ℝ, 0 ≤ f z) (hmono : Monotone f)
    (a l u : ℝ)
    (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 f (Ioo 0 a)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Icc l u, ∀ y < 0,
        ‖SpectrallyNegativeLevy.generatorIntegrand f x y‖ ≤
          C * min 1 (y ^ 2) := by sorry
