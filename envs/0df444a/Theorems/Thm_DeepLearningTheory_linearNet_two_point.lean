-- Prove2me | Theorems.Thm_DeepLearningTheory_linearNet_two_point
-- name    : DeepLearningTheory.linearNet_two_point
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T21:29:37.093635+00:00
-- url     : https://prove2.me/theorems/d3383253-ba64-43b1-b49c-03d6ae377364
-- title:
--   Deep linear network: two-point correlator $\delta_{i_1i_2}C_W^\ell G^{(0)}$ (eqs. 3.12, 3.15)
-- statement:
--   For a zero-bias deep linear network with positive widths at initialization (eq. 3.4), any two inputs $x_{\alpha_1},x_{\alpha_2}$, every layer $\ell\ge1$ and neurons $i_1,i_2$ of that layer,
--
--   $$\mathbb{E}\big[z^{(\ell)}_{i_1;\alpha_1}z^{(\ell)}_{i_2;\alpha_2}\big]=\delta_{i_1i_2}\,(C_W)^{\ell}\,G^{(0)}_{\alpha_1\alpha_2}.$$
--
--   The covariance is multiplied by $C_W$ at each layer, which is the origin of the criticality condition $C_W=1$.
-- source:
--   Daniel A. Roberts and Sho Yaida (with Boris Hanin), *The Principles of Deep Learning Theory*, arXiv:2106.10165v2, https://arxiv.org/abs/2106.10165, §3.2, p. 57, eqs. (3.11)–(3.15) (page numbers are the book's printed page numbers)

import Mathlib
import Definitions.Def_DLT_DeepLinearNetwork

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace DeepLearningTheory

theorem linearNet_two_point {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (hn : ∀ ℓ, 0 < n ℓ) (CW : ℝ≥0)
    (W : Ω → ℕ → ℕ → ℕ → ℝ) (hW : IsLinearNetInit P n CW W) (x₁ x₂ : ℕ → ℝ)
    (ℓ i₁ i₂ : ℕ) (hℓ : 1 ≤ ℓ) (hi₁ : i₁ < n ℓ) (hi₂ : i₂ < n ℓ) :
    ∫ ω, linearPreact n (W ω) x₁ ℓ i₁ * linearPreact n (W ω) x₂ ℓ i₂ ∂P
      = kron i₁ i₂ * (CW : ℝ) ^ ℓ * inputKernel (n 0) x₁ x₂ := by sorry

end DeepLearningTheory
