-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_generatorJump_continuousOn_compact_of_uniform_C2
-- name    : AvramDividend.Classical.avram_wave4_p3_generatorJump_continuousOn_compact_of_uniform_C2
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:37:19.659621+00:00
-- url     : https://prove2.me/theorems/0d8985c3-8a0e-446f-83f7-909795f7b309
-- title:
--   Continuity of source Lévy compensated jump integral under uniform generic C² domination
-- statement:
--   For any globally monotone and nonnegative real test function with C2 local regularity on (0,a), the full source compensated negative-jump integral is continuous on each compact positive reserve interval [l,u], provided its fixed-jump compensated integrands are almost-everywhere continuous in the starting reserve. The analytic engine is a genuinely uniform C min(1,y²) majorant and the actual Levy finite truncated quadratic moment. This is a reusable core for the capped dividend candidate at the optimal barrier, not an assumed harmonicity or stochastic Dynkin formula.
-- source:
--   Source Levy generator and dominated convergence. Proof architecture of accepted scaleFunction_generatorJump_continuousOn_compact_of_ae_continuity UUID cd6079a9; new generic envelope avram_wave4_p3_generator_integrand_uniform_monotone_C2_quadratic_bound; P3 secondary HJB UUID 8d03da6b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p3_generatorJump_continuousOn_compact_of_uniform_C2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ)
    (hnonneg : ∀ z : ℝ, 0 ≤ f z) (hmono : Monotone f)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 f (Ioo 0 a))
    (hjump : ∀ x ∈ Icc l u,
      ∀ᵐ y ∂(X.ν.restrict (Iio 0)),
        ContinuousWithinAt
          (fun z : ℝ => SpectrallyNegativeLevy.generatorIntegrand f z y)
          (Icc l u) x) :
    ContinuousOn
      (fun x : ℝ =>
        ∫ y : ℝ, SpectrallyNegativeLevy.generatorIntegrand f x y
          ∂(X.ν.restrict (Iio 0)))
      (Icc l u) := by sorry
