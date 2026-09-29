-- Prove2me | Theorems.Thm_DeepLearningTheory_mlp_metric_fluctuation_two_point
-- name    : DeepLearningTheory.mlp_metric_fluctuation_two_point
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:00:01.118606+00:00
-- url     : https://prove2.me/theorems/f5f08ed7-b6ef-4d95-8bcc-f09789160fcc
-- title:
--   MLP: fluctuation of the second-layer metric (eq. 4.40)
-- statement:
--   For an MLP at initialization with a measurable activation $\sigma$ of polynomial growth and $n_1\ge1$, let
--
--   $$\widehat{\Delta G}^{(2)}_{\alpha_1\alpha_2}=C_W^{(2)}\,\frac1{n_1}\sum_{j=1}^{n_1}\Big(\sigma^{(1)}_{j;\alpha_1}\sigma^{(1)}_{j;\alpha_2}-\langle\sigma_{\alpha_1}\sigma_{\alpha_2}\rangle_{G^{(1)}}\Big),\qquad\sigma^{(1)}_{j;\alpha}=\sigma\big(z^{(1)}_{j;\alpha}\big),$$
--
--   be the fluctuation of the stochastic second-layer metric around its mean. Then for inputs $x_{\alpha_1},\dots,x_{\alpha_4}$,
--
--   $$\mathbb{E}\Big[\widehat{\Delta G}^{(2)}_{\alpha_1\alpha_2}\widehat{\Delta G}^{(2)}_{\alpha_3\alpha_4}\Big]=\frac1{n_1}\big(C_W^{(2)}\big)^2\Big[\langle\sigma_{\alpha_1}\sigma_{\alpha_2}\sigma_{\alpha_3}\sigma_{\alpha_4}\rangle_{G^{(1)}}-\langle\sigma_{\alpha_1}\sigma_{\alpha_2}\rangle_{G^{(1)}}\langle\sigma_{\alpha_3}\sigma_{\alpha_4}\rangle_{G^{(1)}}\Big]=\frac1{n_1}V^{(2)}_{(\alpha_1\alpha_2)(\alpha_3\alpha_4)}.$$
-- source:
--   Daniel A. Roberts and Sho Yaida (with Boris Hanin), *The Principles of Deep Learning Theory*, arXiv:2106.10165v2, https://arxiv.org/abs/2106.10165, §4.2, p. 81, eqs. (4.36)–(4.40) (page numbers are the book's printed page numbers)

import Mathlib
import Definitions.Def_DLT_DeepLinearNetwork
import Definitions.Def_DLT_MLPInit

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace DeepLearningTheory

theorem mlp_metric_fluctuation_two_point {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (Cb CW : ℕ → ℝ≥0) (σ : ℝ → ℝ)
    (b : Ω → ℕ → ℕ → ℝ) (W : Ω → ℕ → ℕ → ℕ → ℝ) (hinit : IsMLPInit P n Cb CW b W)
    (hσm : Measurable σ) (hσ : HasPolyGrowth σ) (hn₁ : 0 < n 1) (x : Fin 4 → ℕ → ℝ) :
    ∫ ω, ((CW 2 : ℝ) * (1 / (n 1 : ℝ)) * ∑ j ∈ Finset.range (n 1),
          (σ (mlpPreact n σ (b ω) (W ω) (x 0) 1 j) * σ (mlpPreact n σ (b ω) (W ω) (x 1) 1 j)
            - gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x) (fun u => σ (u 0) * σ (u 1)))) *
        ((CW 2 : ℝ) * (1 / (n 1 : ℝ)) * ∑ j ∈ Finset.range (n 1),
          (σ (mlpPreact n σ (b ω) (W ω) (x 2) 1 j) * σ (mlpPreact n σ (b ω) (W ω) (x 3) 1 j)
            - gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x) (fun u => σ (u 2) * σ (u 3)))) ∂P
      = (1 / (n 1 : ℝ)) * (CW 2 : ℝ) ^ 2 *
          (gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x)
              (fun u => σ (u 0) * σ (u 1) * σ (u 2) * σ (u 3))
            - gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x) (fun u => σ (u 0) * σ (u 1)) *
              gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x) (fun u => σ (u 2) * σ (u 3))) := by sorry

end DeepLearningTheory
