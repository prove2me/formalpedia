-- Prove2me | Theorems.Thm_DeepLearningTheory_mlp_first_layer_activation_four_point_same_neuron
-- name    : DeepLearningTheory.mlp_first_layer_activation_four_point_same_neuron
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T21:54:42.612472+00:00
-- url     : https://prove2.me/theorems/4b5e1bbb-0498-4eea-901b-92c2df30fe71
-- title:
--   MLP: four activations on one first-layer neuron (eq. 4.28)
-- statement:
--   For an MLP at initialization with a measurable activation $\sigma$ of polynomial growth, inputs $x_{\alpha_1},\dots,x_{\alpha_4}$ and a first-layer neuron $j$,
--
--   $$\mathbb{E}\Big[\prod_{a=1}^4\sigma\big(z^{(1)}_{j;\alpha_a}\big)\Big]=\langle\sigma_{\alpha_1}\sigma_{\alpha_2}\sigma_{\alpha_3}\sigma_{\alpha_4}\rangle_{G^{(1)}}.$$
-- source:
--   Daniel A. Roberts and Sho Yaida (with Boris Hanin), *The Principles of Deep Learning Theory*, arXiv:2106.10165v2, https://arxiv.org/abs/2106.10165, §4.1, p. 79, eq. (4.28) (page numbers are the book's printed page numbers)

import Mathlib
import Definitions.Def_DLT_DeepLinearNetwork
import Definitions.Def_DLT_MLPInit

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace DeepLearningTheory

theorem mlp_first_layer_activation_four_point_same_neuron {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (Cb CW : ℕ → ℝ≥0) (σ : ℝ → ℝ)
    (b : Ω → ℕ → ℕ → ℝ) (W : Ω → ℕ → ℕ → ℕ → ℝ) (hinit : IsMLPInit P n Cb CW b W)
    (hσm : Measurable σ) (hσ : HasPolyGrowth σ) (x : Fin 4 → ℕ → ℝ) (j : ℕ) (hj : j < n 1) :
    ∫ ω, σ (mlpPreact n σ (b ω) (W ω) (x 0) 1 j) * σ (mlpPreact n σ (b ω) (W ω) (x 1) 1 j) *
        σ (mlpPreact n σ (b ω) (W ω) (x 2) 1 j) * σ (mlpPreact n σ (b ω) (W ω) (x 3) 1 j) ∂P
      = gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x)
          (fun u => σ (u 0) * σ (u 1) * σ (u 2) * σ (u 3)) := by sorry

end DeepLearningTheory
