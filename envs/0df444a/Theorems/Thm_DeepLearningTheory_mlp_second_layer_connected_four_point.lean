-- Prove2me | Theorems.Thm_DeepLearningTheory_mlp_second_layer_connected_four_point
-- name    : DeepLearningTheory.mlp_second_layer_connected_four_point
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:08:54.116742+00:00
-- url     : https://prove2.me/theorems/7cb5d6fc-f285-441a-a8e3-f703c75d3a12
-- title:
--   MLP: second-layer connected four-point correlator and the four-point vertex (eq. 4.43)
-- statement:
--   **Genesis of non-Gaussianity.** Consider an MLP at initialization (eqs. 4.3–4.4) with a measurable activation $\sigma$ of polynomial growth and $n_1\ge1$. For inputs $x_{\alpha_1},\dots,x_{\alpha_4}$ (not necessarily distinct) and second-layer neurons $i_1,\dots,i_4$, the connected four-point correlator of the second-layer preactivations,
--
--   $$\mathbb{E}\big[z^{(2)}_{i_1;\alpha_1}z^{(2)}_{i_2;\alpha_2}z^{(2)}_{i_3;\alpha_3}z^{(2)}_{i_4;\alpha_4}\big]\Big|_{\text{connected}}=\mathbb{E}\big[z_1z_2z_3z_4\big]-\mathbb{E}[z_1z_2]\mathbb{E}[z_3z_4]-\mathbb{E}[z_1z_3]\mathbb{E}[z_2z_4]-\mathbb{E}[z_1z_4]\mathbb{E}[z_2z_3]$$
--
--   (with $z_a=z^{(2)}_{i_a;\alpha_a}$), equals
--
--   $$\frac{1}{n_1}\Big[\delta_{i_1i_2}\delta_{i_3i_4}V^{(2)}_{(\alpha_1\alpha_2)(\alpha_3\alpha_4)}+\delta_{i_1i_3}\delta_{i_2i_4}V^{(2)}_{(\alpha_1\alpha_3)(\alpha_2\alpha_4)}+\delta_{i_1i_4}\delta_{i_2i_3}V^{(2)}_{(\alpha_1\alpha_4)(\alpha_2\alpha_3)}\Big],$$
--
--   where the **four-point vertex** is
--
--   $$V^{(2)}_{(\alpha_1\alpha_2)(\alpha_3\alpha_4)}=\big(C_W^{(2)}\big)^2\Big[\langle\sigma_{\alpha_1}\sigma_{\alpha_2}\sigma_{\alpha_3}\sigma_{\alpha_4}\rangle_{G^{(1)}}-\langle\sigma_{\alpha_1}\sigma_{\alpha_2}\rangle_{G^{(1)}}\langle\sigma_{\alpha_3}\sigma_{\alpha_4}\rangle_{G^{(1)}}\Big].$$
--
--   The second-layer distribution is therefore non-Gaussian at finite width, with non-Gaussianity suppressed by $1/n_1$.
--
--   **Formalization Note** All Gaussian averages are taken with the first-layer metric of the four inputs $x_{\alpha_1},\dots,x_{\alpha_4}$, which may be singular.
-- source:
--   Daniel A. Roberts and Sho Yaida (with Boris Hanin), *The Principles of Deep Learning Theory*, arXiv:2106.10165v2, https://arxiv.org/abs/2106.10165, §4.2, pp. 81–82, eqs. (4.40), (4.42), (4.43) (page numbers are the book's printed page numbers)

import Mathlib
import Definitions.Def_DLT_DeepLinearNetwork
import Definitions.Def_DLT_MLPInit

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace DeepLearningTheory

theorem mlp_second_layer_connected_four_point {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (Cb CW : ℕ → ℝ≥0) (σ : ℝ → ℝ)
    (b : Ω → ℕ → ℕ → ℝ) (W : Ω → ℕ → ℕ → ℕ → ℝ) (hinit : IsMLPInit P n Cb CW b W)
    (hσm : Measurable σ) (hσ : HasPolyGrowth σ) (hn₁ : 0 < n 1) (x : Fin 4 → ℕ → ℝ) (i : Fin 4 → ℕ) (hi : ∀ a, i a < n 2) :
    (∫ ω, mlpPreact n σ (b ω) (W ω) (x 0) 2 (i 0) * mlpPreact n σ (b ω) (W ω) (x 1) 2 (i 1) *
        mlpPreact n σ (b ω) (W ω) (x 2) 2 (i 2) * mlpPreact n σ (b ω) (W ω) (x 3) 2 (i 3) ∂P)
      - (∫ ω, mlpPreact n σ (b ω) (W ω) (x 0) 2 (i 0) * mlpPreact n σ (b ω) (W ω) (x 1) 2 (i 1) ∂P) * (∫ ω, mlpPreact n σ (b ω) (W ω) (x 2) 2 (i 2) * mlpPreact n σ (b ω) (W ω) (x 3) 2 (i 3) ∂P)
      - (∫ ω, mlpPreact n σ (b ω) (W ω) (x 0) 2 (i 0) * mlpPreact n σ (b ω) (W ω) (x 2) 2 (i 2) ∂P) * (∫ ω, mlpPreact n σ (b ω) (W ω) (x 1) 2 (i 1) * mlpPreact n σ (b ω) (W ω) (x 3) 2 (i 3) ∂P)
      - (∫ ω, mlpPreact n σ (b ω) (W ω) (x 0) 2 (i 0) * mlpPreact n σ (b ω) (W ω) (x 3) 2 (i 3) ∂P) * (∫ ω, mlpPreact n σ (b ω) (W ω) (x 1) 2 (i 1) * mlpPreact n σ (b ω) (W ω) (x 2) 2 (i 2) ∂P)
      = (1 / (n 1 : ℝ)) *
          (kron (i 0) (i 1) * kron (i 2) (i 3) * ((CW 2 : ℝ) ^ 2 *
            (gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x)
                (fun u => σ (u 0) * σ (u 1) * σ (u 2) * σ (u 3))
              - gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x) (fun u => σ (u 0) * σ (u 1)) *
                gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x) (fun u => σ (u 2) * σ (u 3))))
          + kron (i 0) (i 2) * kron (i 1) (i 3) * ((CW 2 : ℝ) ^ 2 *
            (gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x)
                (fun u => σ (u 0) * σ (u 1) * σ (u 2) * σ (u 3))
              - gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x) (fun u => σ (u 0) * σ (u 2)) *
                gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x) (fun u => σ (u 1) * σ (u 3))))
          + kron (i 0) (i 3) * kron (i 1) (i 2) * ((CW 2 : ℝ) ^ 2 *
            (gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x)
                (fun u => σ (u 0) * σ (u 1) * σ (u 2) * σ (u 3))
              - gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x) (fun u => σ (u 0) * σ (u 3)) *
                gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x) (fun u => σ (u 1) * σ (u 2))))) := by sorry

end DeepLearningTheory
