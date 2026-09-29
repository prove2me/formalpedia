-- Prove2me | Theorems.Thm_DeepLearningTheory_mlp_first_layer_activation_two_point
-- name    : DeepLearningTheory.mlp_first_layer_activation_two_point
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T21:52:13.148312+00:00
-- url     : https://prove2.me/theorems/26de32c3-dae2-4b7f-b59c-f910f9e04e4e
-- title:
--   MLP: $\mathbb{E}[\sigma(z^{(1)}_{i;\alpha_1})\sigma(z^{(1)}_{i;\alpha_2})]=\langle\sigma_{\alpha_1}\sigma_{\alpha_2}\rangle_{G^{(1)}}$ (eq. 4.27)
-- statement:
--   For an MLP at initialization with a measurable activation $\sigma$ of polynomial growth, two inputs $x_{\alpha_1},x_{\alpha_2}$ and a first-layer neuron $j$,
--
--   $$\mathbb{E}\big[\sigma\big(z^{(1)}_{j;\alpha_1}\big)\sigma\big(z^{(1)}_{j;\alpha_2}\big)\big]=\langle\sigma_{\alpha_1}\sigma_{\alpha_2}\rangle_{G^{(1)}},$$
--
--   where $\langle\cdot\rangle_{G^{(1)}}$ is the expectation over a centered Gaussian vector $(z_{\alpha_1},z_{\alpha_2})$ with covariance given by the first-layer metric, and $\sigma_\alpha=\sigma(z_\alpha)$.
-- source:
--   Daniel A. Roberts and Sho Yaida (with Boris Hanin), *The Principles of Deep Learning Theory*, arXiv:2106.10165v2, https://arxiv.org/abs/2106.10165, §4.1, pp. 78–79, eqs. (4.24)–(4.27) (page numbers are the book's printed page numbers)

import Mathlib
import Definitions.Def_DLT_DeepLinearNetwork
import Definitions.Def_DLT_MLPInit

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace DeepLearningTheory

theorem mlp_first_layer_activation_two_point {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (Cb CW : ℕ → ℝ≥0) (σ : ℝ → ℝ)
    (b : Ω → ℕ → ℕ → ℝ) (W : Ω → ℕ → ℕ → ℕ → ℝ) (hinit : IsMLPInit P n Cb CW b W)
    (hσm : Measurable σ) (hσ : HasPolyGrowth σ) (x : Fin 2 → ℕ → ℝ) (j : ℕ) (hj : j < n 1) :
    ∫ ω, σ (mlpPreact n σ (b ω) (W ω) (x 0) 1 j) * σ (mlpPreact n σ (b ω) (W ω) (x 1) 1 j) ∂P
      = gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x) (fun u => σ (u 0) * σ (u 1)) := by sorry

end DeepLearningTheory
