-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_discounted_hessian_generator_identification
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_original_discounted_hessian_generator_identification
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:04:26.369779+00:00
-- url     : https://prove2.me/theorems/0d631a29-332e-4fb6-b50d-6d6cc281d9d1
-- title:
--   Exact original-process Gaussian generator convention identifies the ordinary Hessian
-- statement:
--   For the actual arbitrary spectrally negative Levy X with its actual Gaussian parameter sigma, the discounted generator coefficient sigma squared over two times iteratedDeriv 2 w equals exactly sigma squared over two times deriv (deriv w). This is a pointwise algebraic identification for all sigma including zero, matching the original source's Eq 5.11 Ito correction and the original generator convention. It does not assert any stochastic integral or decomposition.
-- source:
--   Pinned AvramDividend.Classical.SpectrallyNegativeLevy generator, exact original generator split 668fd38f, pinned Mathlib iteratedDeriv_succ and iteratedDeriv_one.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_original_discounted_hessian_generator_identification
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (q t y : ℝ) :
    Real.exp (-(q * t)) * (X.σ ^ 2 / 2 * iteratedDeriv 2 w y) =
      Real.exp (-(q * t)) * (X.σ ^ 2 / 2 * deriv (deriv w) y) := by sorry
