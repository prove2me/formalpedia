-- Prove2me | Theorems.Thm_DeepLearningTheory_mlp_first_layer_two_point
-- name    : DeepLearningTheory.mlp_first_layer_two_point
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T21:28:15.033992+00:00
-- url     : https://prove2.me/theorems/8d33db27-68f0-47fa-a99d-aa98a1510e09
-- title:
--   MLP: first-layer two-point correlator $\delta_{i_1i_2}G^{(1)}_{\alpha_1\alpha_2}$ (eqs. 4.7–4.8)
-- statement:
--   For an MLP at initialization, any two inputs $x_{\alpha_1},x_{\alpha_2}$ and first-layer neurons $i_1,i_2$,
--
--   $$\mathbb{E}\big[z^{(1)}_{i_1;\alpha_1}z^{(1)}_{i_2;\alpha_2}\big]=\delta_{i_1i_2}\,G^{(1)}_{\alpha_1\alpha_2},\qquad G^{(1)}_{\alpha_1\alpha_2}=C_b^{(1)}+C_W^{(1)}\frac1{n_0}\sum_{j=1}^{n_0}x_{j;\alpha_1}x_{j;\alpha_2}.$$
-- source:
--   Daniel A. Roberts and Sho Yaida (with Boris Hanin), *The Principles of Deep Learning Theory*, arXiv:2106.10165v2, https://arxiv.org/abs/2106.10165, §4.1, p. 74, eqs. (4.7)–(4.8) (page numbers are the book's printed page numbers)

import Mathlib
import Definitions.Def_DLT_DeepLinearNetwork
import Definitions.Def_DLT_MLPInit

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace DeepLearningTheory

theorem mlp_first_layer_two_point {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (Cb CW : ℕ → ℝ≥0) (σ : ℝ → ℝ)
    (b : Ω → ℕ → ℕ → ℝ) (W : Ω → ℕ → ℕ → ℕ → ℝ) (hinit : IsMLPInit P n Cb CW b W)
    (x₁ x₂ : ℕ → ℝ) (i₁ i₂ : ℕ) (hi₁ : i₁ < n 1) (hi₂ : i₂ < n 1) :
    ∫ ω, mlpPreact n σ (b ω) (W ω) x₁ 1 i₁ * mlpPreact n σ (b ω) (W ω) x₂ 1 i₂ ∂P
      = kron i₁ i₂ * ((Cb 1 : ℝ) + (CW 1 : ℝ) * inputKernel (n 0) x₁ x₂) := by sorry

end DeepLearningTheory
