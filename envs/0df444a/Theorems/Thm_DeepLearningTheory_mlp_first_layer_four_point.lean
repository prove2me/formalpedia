-- Prove2me | Theorems.Thm_DeepLearningTheory_mlp_first_layer_four_point
-- name    : DeepLearningTheory.mlp_first_layer_four_point
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T21:31:29.502886+00:00
-- url     : https://prove2.me/theorems/a2c47085-8e8f-4775-9625-ab235329ce0b
-- title:
--   MLP: first-layer four-point correlator (eq. 4.9)
-- statement:
--   For an MLP at initialization, inputs $x_{\alpha_1},\dots,x_{\alpha_4}$ (not necessarily distinct) and first-layer neurons $i_1,\dots,i_4$,
--
--   $$\mathbb{E}\big[z^{(1)}_{i_1;\alpha_1}z^{(1)}_{i_2;\alpha_2}z^{(1)}_{i_3;\alpha_3}z^{(1)}_{i_4;\alpha_4}\big]=\delta_{i_1i_2}\delta_{i_3i_4}G^{(1)}_{\alpha_1\alpha_2}G^{(1)}_{\alpha_3\alpha_4}+\delta_{i_1i_3}\delta_{i_2i_4}G^{(1)}_{\alpha_1\alpha_3}G^{(1)}_{\alpha_2\alpha_4}+\delta_{i_1i_4}\delta_{i_2i_3}G^{(1)}_{\alpha_1\alpha_4}G^{(1)}_{\alpha_2\alpha_3}.$$
--
--   Equivalently, the connected four-point correlator of the first layer vanishes (eq. 4.10).
-- source:
--   Daniel A. Roberts and Sho Yaida (with Boris Hanin), *The Principles of Deep Learning Theory*, arXiv:2106.10165v2, https://arxiv.org/abs/2106.10165, §4.1, p. 75, eq. (4.9) (page numbers are the book's printed page numbers)

import Mathlib
import Definitions.Def_DLT_DeepLinearNetwork
import Definitions.Def_DLT_MLPInit

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace DeepLearningTheory

theorem mlp_first_layer_four_point {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (Cb CW : ℕ → ℝ≥0) (σ : ℝ → ℝ)
    (b : Ω → ℕ → ℕ → ℝ) (W : Ω → ℕ → ℕ → ℕ → ℝ) (hinit : IsMLPInit P n Cb CW b W)
    (x : Fin 4 → ℕ → ℝ) (i : Fin 4 → ℕ) (hi : ∀ a, i a < n 1) :
    ∫ ω, mlpPreact n σ (b ω) (W ω) (x 0) 1 (i 0) * mlpPreact n σ (b ω) (W ω) (x 1) 1 (i 1) *
        mlpPreact n σ (b ω) (W ω) (x 2) 1 (i 2) * mlpPreact n σ (b ω) (W ω) (x 3) 1 (i 3) ∂P
      = kron (i 0) (i 1) * kron (i 2) (i 3) *
            firstLayerMetric (Cb 1) (CW 1) (n 0) x 0 1 * firstLayerMetric (Cb 1) (CW 1) (n 0) x 2 3
        + kron (i 0) (i 2) * kron (i 1) (i 3) *
            firstLayerMetric (Cb 1) (CW 1) (n 0) x 0 2 * firstLayerMetric (Cb 1) (CW 1) (n 0) x 1 3
        + kron (i 0) (i 3) * kron (i 1) (i 2) *
            firstLayerMetric (Cb 1) (CW 1) (n 0) x 0 3 * firstLayerMetric (Cb 1) (CW 1) (n 0) x 1 2
      := by sorry

end DeepLearningTheory
