-- Prove2me | Theorems.Thm_DeepLearningTheory_mlp_first_layer_activation_four_point_two_neurons
-- name    : DeepLearningTheory.mlp_first_layer_activation_four_point_two_neurons
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T21:56:53.317716+00:00
-- url     : https://prove2.me/theorems/6128be73-1023-47f0-b9f6-0da74b6978d8
-- title:
--   MLP: activations on two distinct first-layer neurons factorize (eq. 4.29)
-- statement:
--   For an MLP at initialization with a measurable activation $\sigma$ of polynomial growth, inputs $x_{\alpha_1},\dots,x_{\alpha_4}$ and two distinct first-layer neurons $j\ne k$,
--
--   $$\mathbb{E}\big[\sigma\big(z^{(1)}_{j;\alpha_1}\big)\sigma\big(z^{(1)}_{j;\alpha_2}\big)\sigma\big(z^{(1)}_{k;\alpha_3}\big)\sigma\big(z^{(1)}_{k;\alpha_4}\big)\big]=\langle\sigma_{\alpha_1}\sigma_{\alpha_2}\rangle_{G^{(1)}}\,\langle\sigma_{\alpha_3}\sigma_{\alpha_4}\rangle_{G^{(1)}}.$$
--
--   Neurons in the first layer do not interact.
-- source:
--   Daniel A. Roberts and Sho Yaida (with Boris Hanin), *The Principles of Deep Learning Theory*, arXiv:2106.10165v2, https://arxiv.org/abs/2106.10165, §4.1, p. 79, eq. (4.29) (page numbers are the book's printed page numbers)

import Mathlib
import Definitions.Def_DLT_DeepLinearNetwork
import Definitions.Def_DLT_MLPInit

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace DeepLearningTheory

theorem mlp_first_layer_activation_four_point_two_neurons {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (Cb CW : ℕ → ℝ≥0) (σ : ℝ → ℝ)
    (b : Ω → ℕ → ℕ → ℝ) (W : Ω → ℕ → ℕ → ℕ → ℝ) (hinit : IsMLPInit P n Cb CW b W)
    (hσm : Measurable σ) (hσ : HasPolyGrowth σ) (x : Fin 4 → ℕ → ℝ) (j k : ℕ) (hj : j < n 1) (hk : k < n 1) (hjk : j ≠ k) :
    ∫ ω, σ (mlpPreact n σ (b ω) (W ω) (x 0) 1 j) * σ (mlpPreact n σ (b ω) (W ω) (x 1) 1 j) *
        σ (mlpPreact n σ (b ω) (W ω) (x 2) 1 k) * σ (mlpPreact n σ (b ω) (W ω) (x 3) 1 k) ∂P
      = gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x) (fun u => σ (u 0) * σ (u 1)) *
          gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x) (fun u => σ (u 2) * σ (u 3)) := by sorry

end DeepLearningTheory
