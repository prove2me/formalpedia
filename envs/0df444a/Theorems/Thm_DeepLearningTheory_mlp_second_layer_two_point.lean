-- Prove2me | Theorems.Thm_DeepLearningTheory_mlp_second_layer_two_point
-- name    : DeepLearningTheory.mlp_second_layer_two_point
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:02:15.188159+00:00
-- url     : https://prove2.me/theorems/897eb437-bec7-4bec-b53a-840d55bb09b4
-- title:
--   MLP: second-layer two-point correlator (eq. 4.41)
-- statement:
--   For an MLP at initialization with a measurable activation $\sigma$ of polynomial growth and $n_1\ge1$, two inputs $x_{\alpha_1},x_{\alpha_2}$ and second-layer neurons $i_1,i_2$,
--
--   $$\mathbb{E}\big[z^{(2)}_{i_1;\alpha_1}z^{(2)}_{i_2;\alpha_2}\big]=\delta_{i_1i_2}\Big(C_b^{(2)}+C_W^{(2)}\,\langle\sigma_{\alpha_1}\sigma_{\alpha_2}\rangle_{G^{(1)}}\Big).$$
--
--   This is the first step of the kernel recursion $G^{(\ell+1)}=C_b+C_W\langle\sigma\sigma\rangle_{G^{(\ell)}}$.
-- source:
--   Daniel A. Roberts and Sho Yaida (with Boris Hanin), *The Principles of Deep Learning Theory*, arXiv:2106.10165v2, https://arxiv.org/abs/2106.10165, §4.2, pp. 81–82, eqs. (4.37), (4.41) (page numbers are the book's printed page numbers)

import Mathlib
import Definitions.Def_DLT_DeepLinearNetwork
import Definitions.Def_DLT_MLPInit

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace DeepLearningTheory

theorem mlp_second_layer_two_point {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (Cb CW : ℕ → ℝ≥0) (σ : ℝ → ℝ)
    (b : Ω → ℕ → ℕ → ℝ) (W : Ω → ℕ → ℕ → ℕ → ℝ) (hinit : IsMLPInit P n Cb CW b W)
    (hσm : Measurable σ) (hσ : HasPolyGrowth σ) (hn₁ : 0 < n 1) (x : Fin 2 → ℕ → ℝ) (i₁ i₂ : ℕ) (hi₁ : i₁ < n 2) (hi₂ : i₂ < n 2) :
    ∫ ω, mlpPreact n σ (b ω) (W ω) (x 0) 2 i₁ * mlpPreact n σ (b ω) (W ω) (x 1) 2 i₂ ∂P
      = kron i₁ i₂ * ((Cb 2 : ℝ) + (CW 2 : ℝ) *
          gaussAvg (firstLayerMetric (Cb 1) (CW 1) (n 0) x) (fun u => σ (u 0) * σ (u 1))) := by sorry

end DeepLearningTheory
