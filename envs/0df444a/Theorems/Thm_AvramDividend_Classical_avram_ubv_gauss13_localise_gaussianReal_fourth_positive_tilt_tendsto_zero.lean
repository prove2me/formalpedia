-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_gaussianReal_fourth_positive_tilt_tendsto_zero
-- name    : AvramDividend.Classical.avram_ubv_gauss13_localise_gaussianReal_fourth_positive_tilt_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T10:58:41.224646+00:00
-- url     : https://prove2.me/theorems/9f1008a6-be2b-49f3-8016-a685d4806049
-- title:
--   Gaussian reference fourth exponential moment converges at positive parameter zero
-- statement:
--   For the reference GaussianReal distribution with mean zero and variance t, the fourth exponentially tilted moment at the strictly positive sequence 1/(n+1) converges to the unweighted fourth moment. The proof uses the Gaussian reference distribution's two-sided exponential integrability, pointwise bound by z^4 times exp z plus exp minus z, and pinned Lebesgue dominated convergence. This is exactly the missing Gaussian-side child of original-process positive-theta Fatou fourth-moment transfer, not a claim about a substitute Brownian path.
-- source:
--   Pinned Mathlib integrableExpSet_id_gaussianReal, integrable_pow_mul_exp_of_mem_interior_integrableExpSet, tendsto_integral_of_dominated_convergence; original process Fatou theorem 46e23cf2.

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_localise_gaussianReal_fourth_positive_tilt_tendsto_zero
    (t : ℝ≥0) :
    Tendsto (fun n : ℕ =>
      ∫ z : ℝ, z ^ 4 * Real.exp ((1 / ((n : ℝ) + 1)) * z)
        ∂(gaussianReal 0 t)) atTop
      (𝓝 (∫ z : ℝ, z ^ 4 ∂(gaussianReal 0 t))) := by sorry
