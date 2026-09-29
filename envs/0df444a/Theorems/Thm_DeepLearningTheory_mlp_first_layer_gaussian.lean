-- Prove2me | Theorems.Thm_DeepLearningTheory_mlp_first_layer_gaussian
-- name    : DeepLearningTheory.mlp_first_layer_gaussian
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T21:42:29.096382+00:00
-- url     : https://prove2.me/theorems/0c669d88-29bf-424c-8e68-1076843065fd
-- title:
--   MLP: the first layer is exactly Gaussian (eq. 4.23)
-- statement:
--   For an MLP at initialization and a dataset of $D$ inputs $x_{\alpha}$, $\alpha=1,\dots,D$, the $(n_1D)$-dimensional random vector of first-layer preactivations $\big(z^{(1)}_{i;\alpha}\big)_{i\le n_1,\ \alpha\le D}$ is a centered Gaussian with covariance
--
--   $$\mathbb{E}\big[z^{(1)}_{i_1;\alpha_1}z^{(1)}_{i_2;\alpha_2}\big]=\delta_{i_1i_2}\,G^{(1)}_{\alpha_1\alpha_2}.$$
--
--   In particular, different neurons are independent in the first layer.
--
--   **Formalization Note** The law is stated as a pushforward measure on Euclidean space indexed by (neuron, sample) pairs and compared with Mathlib's `multivariateGaussian`, so that a singular metric (e.g. repeated inputs), where the density (4.23) does not exist, is covered.
-- source:
--   Daniel A. Roberts and Sho Yaida (with Boris Hanin), *The Principles of Deep Learning Theory*, arXiv:2106.10165v2, https://arxiv.org/abs/2106.10165, §4.1, pp. 75–77, eqs. (4.13), (4.14), (4.23) (page numbers are the book's printed page numbers)

import Mathlib
import Definitions.Def_DLT_DeepLinearNetwork
import Definitions.Def_DLT_MLPInit

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace DeepLearningTheory

theorem mlp_first_layer_gaussian {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (Cb CW : ℕ → ℝ≥0) (σ : ℝ → ℝ)
    (b : Ω → ℕ → ℕ → ℝ) (W : Ω → ℕ → ℕ → ℕ → ℝ) (hinit : IsMLPInit P n Cb CW b W)
    {D : ℕ} (x : Fin D → ℕ → ℝ) :
    P.map (fun ω => WithLp.toLp 2
        (fun p : Fin (n 1) × Fin D => mlpPreact n σ (b ω) (W ω) (x p.2) 1 (p.1 : ℕ)))
      = multivariateGaussian 0
          (fun p q : Fin (n 1) × Fin D =>
            kron p.1 q.1 * firstLayerMetric (Cb 1) (CW 1) (n 0) x p.2 q.2) := by sorry

end DeepLearningTheory
