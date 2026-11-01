-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_generator_integrand_uniform_near_C2_quadratic_bound
-- name    : AvramDividend.Classical.avram_wave4_p3_generator_integrand_uniform_near_C2_quadratic_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:30:34.993622+00:00
-- url     : https://prove2.me/theorems/485f09e2-781b-4471-a0f7-93c1a4abffb4
-- title:
--   Uniform C² compensated small-jump Taylor bound on a compact interval for arbitrary test functions
-- statement:
--   For the original spectrally negative Levy triplet, any twice continuously differentiable real test function on (0,a) has one uniform quadratic compensated-jump bound for all starting reserves in a compact interval [l,u] inside (0,a). The bound is derived by a compact supremum of the true second derivative and a first-order Taylor remainder, and is independent of scale-function or stochastic harmonicity assumptions. It is the missing generic near-jump envelope needed to prove right-continuity of the true generator of vcstar at the positive barrier under the globally positive C2 branch.
-- source:
--   Taylor theorem with Lagrange remainder, using pinned Mathlib's taylor_mean_remainder_lagrange_iteratedDeriv. Faithful generalisation of accepted AvramDividend.Classical.scaleFunction_uniform_near_zero_bound_on_compact UUID df9f9ec7; P3 endpoint HJB target 8d03da6b via uniform Levy dominated convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p3_generator_integrand_uniform_near_C2_quadratic_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (a l u : ℝ)
    (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 f (Ioo 0 a)) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ min l 1 ∧ 0 ≤ C ∧
      ∀ x ∈ Icc l u, ∀ y ∈ Ioo (-r) 0,
        ‖SpectrallyNegativeLevy.generatorIntegrand f x y‖ ≤ C * y ^ 2 := by sorry
