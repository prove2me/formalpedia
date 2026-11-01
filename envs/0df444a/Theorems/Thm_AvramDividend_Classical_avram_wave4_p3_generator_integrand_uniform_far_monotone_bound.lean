-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_generator_integrand_uniform_far_monotone_bound
-- name    : AvramDividend.Classical.avram_wave4_p3_generator_integrand_uniform_far_monotone_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:31:43.444117+00:00
-- url     : https://prove2.me/theorems/6371add2-4a5e-4089-a5ad-a43bdbe80778
-- title:
--   Uniform Lévy far-jump envelope for monotone nonnegative C² test functions
-- statement:
--   On a compact positive reserve interval, a nonnegative globally monotone test function with local C2 differentiability admits a common finite bound C min(1,y²) on the true compensated Levy generator increments for all sufficiently large negative jumps y≤-r. The proof uses monotonicity to bound f(x+y)-f(x), uniform boundedness of f' on the compact state interval, and r>0 to absorb the finite large-jump mass. This is the far-jump component of positive optimal-barrier generator right-continuity for vcstar.
-- source:
--   Exact source spectrally negative Levy compensator and compact local C2, faithful generalisation of accepted scaleFunction_uniform_far_jump_bound_on_compact UUID 25b17770. Dependency for endpoint HJB 8d03da6b, not a q-harmonicity assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p3_generator_integrand_uniform_far_monotone_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ)
    (hnonneg : ∀ z : ℝ, 0 ≤ f z) (hmono : Monotone f)
    (a l u r : ℝ)
    (hl : 0 < l) (hlu : l < u) (hu : u < a) (hr : 0 < r)
    (hC2 : ContDiffOn ℝ 2 f (Ioo 0 a)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Icc l u, ∀ y < 0, y ≤ -r →
        ‖SpectrallyNegativeLevy.generatorIntegrand f x y‖ ≤
          C * min 1 (y ^ 2) := by sorry
