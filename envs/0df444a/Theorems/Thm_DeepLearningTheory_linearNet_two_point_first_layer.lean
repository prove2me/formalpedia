-- Prove2me | Theorems.Thm_DeepLearningTheory_linearNet_two_point_first_layer
-- name    : DeepLearningTheory.linearNet_two_point_first_layer
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T21:27:51.917983+00:00
-- url     : https://prove2.me/theorems/27d42c66-32b2-4d53-b1f8-ce61b96083f9
-- title:
--   Deep linear network: first-layer two-point correlator (eq. 3.10)
-- statement:
--   For a zero-bias deep linear network at initialization (eq. 3.4), any two inputs $x_{\alpha_1},x_{\alpha_2}\in\mathbb{R}^{n_0}$ and any first-layer neurons $i_1,i_2$,
--
--   $$\mathbb{E}\big[z^{(1)}_{i_1;\alpha_1}z^{(1)}_{i_2;\alpha_2}\big]=\delta_{i_1i_2}\,C_W\,G^{(0)}_{\alpha_1\alpha_2},\qquad G^{(0)}_{\alpha_1\alpha_2}=\frac1{n_0}\sum_{j=1}^{n_0}x_{j;\alpha_1}x_{j;\alpha_2}.$$
-- source:
--   Daniel A. Roberts and Sho Yaida (with Boris Hanin), *The Principles of Deep Learning Theory*, arXiv:2106.10165v2, https://arxiv.org/abs/2106.10165, §3.2, p. 56, eqs. (3.8)–(3.10) (page numbers are the book's printed page numbers)

import Mathlib
import Definitions.Def_DLT_DeepLinearNetwork

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace DeepLearningTheory

theorem linearNet_two_point_first_layer {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (CW : ℝ≥0) (W : Ω → ℕ → ℕ → ℕ → ℝ)
    (hW : IsLinearNetInit P n CW W) (x₁ x₂ : ℕ → ℝ) (i₁ i₂ : ℕ)
    (hi₁ : i₁ < n 1) (hi₂ : i₂ < n 1) :
    ∫ ω, linearPreact n (W ω) x₁ 1 i₁ * linearPreact n (W ω) x₂ 1 i₂ ∂P
      = kron i₁ i₂ * (CW : ℝ) * inputKernel (n 0) x₁ x₂ := by sorry

end DeepLearningTheory
