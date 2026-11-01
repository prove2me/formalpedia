-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_generator_residual_continuousOn_compact_of_monotone_global_C2
-- name    : AvramDividend.Classical.avram_wave4_p3_generator_residual_continuousOn_compact_of_monotone_global_C2
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:38:22.782985+00:00
-- url     : https://prove2.me/theorems/d574f843-262d-415e-aa5c-2d43606672f5
-- title:
--   True Lévy generator residual continuity on compact reserves for globally continuous monotone C² functions
-- statement:
--   If an original spectrally negative Levy generator acts on a globally continuous, monotone nonnegative real function with C2 regularity on a positive state interval, its true discounted compensated generator residual is continuous on every compact subinterval. This follows from the generic uniform quadratic Levy jump envelope, dominated convergence, and continuity of the drift and Gaussian derivative terms. In the pure-jump unbounded-variation positive-barrier case, the zero-origin barrier candidate meets these regularity conditions. This is a source-faithful missing endpoint continuity interface, not a harmonicity assumption.
-- source:
--   Actual source Levy generator, accepted generatorIntegrand_continuousAt_of_continuous UUID 93c5e7b5 and generator_residual_continuousOn_compact_of_C2_jump_continuity UUID d1495532; new generic P3 jump continuity child. Parent P3 8d03da6b and generator 91803827.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p3_generator_residual_continuousOn_compact_of_monotone_global_C2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (f : ℝ → ℝ)
    (hnonneg : ∀ z : ℝ, 0 ≤ f z) (hmono : Monotone f)
    (hcont : Continuous f)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 f (Ioo 0 a)) :
    ContinuousOn
      (fun x : ℝ => X.generator f x - q * f x) (Icc l u) := by sorry
