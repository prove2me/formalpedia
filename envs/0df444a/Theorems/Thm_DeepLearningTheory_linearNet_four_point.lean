-- Prove2me | Theorems.Thm_DeepLearningTheory_linearNet_four_point
-- name    : DeepLearningTheory.linearNet_four_point
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T21:52:05.304815+00:00
-- url     : https://prove2.me/theorems/bb2a14c2-e7c7-4d1d-b242-bcb0f8c605bd
-- title:
--   Deep linear network: exact four-point correlator at initialization (eqs. 3.21, 3.25)
-- statement:
--   **Exact four-point correlator of a deep linear network.** Consider a zero-bias deep linear network with positive widths $n_0,n_1,\dots$ whose weights are initialized independently with $W^{(\ell)}_{ij}\sim\mathcal{N}(0,C_W/n_{\ell-1})$ (eq. 3.4). For a single input $x\in\mathbb{R}^{n_0}$, every layer $\ell\ge1$ and neurons $i_1,\dots,i_4$ of that layer,
--
--   $$\mathbb{E}\big[z^{(\ell)}_{i_1}z^{(\ell)}_{i_2}z^{(\ell)}_{i_3}z^{(\ell)}_{i_4}\big]=(\delta_{i_1i_2}\delta_{i_3i_4}+\delta_{i_1i_3}\delta_{i_2i_4}+\delta_{i_1i_4}\delta_{i_2i_3})\;C_W^{2\ell}\Big[\prod_{\ell'=1}^{\ell-1}\Big(1+\frac{2}{n_{\ell'}}\Big)\Big]\big(G^{(0)}_2\big)^2,$$
--
--   where $G^{(0)}_2=\frac1{n_0}\sum_{j=1}^{n_0}x_j^2$.
--
--   In the infinite-width limit the bracket tends to $1$ and the correlator becomes the Gaussian (Wick) value; at finite width the deviation grows with depth, controlled by the depth-to-width ratio.
-- source:
--   Daniel A. Roberts and Sho Yaida (with Boris Hanin), *The Principles of Deep Learning Theory*, arXiv:2106.10165v2, https://arxiv.org/abs/2106.10165, §3.3, p. 61, eqs. (3.21), (3.22), (3.25) (page numbers are the book's printed page numbers)

import Mathlib
import Definitions.Def_DLT_DeepLinearNetwork

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace DeepLearningTheory

theorem linearNet_four_point {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (hn : ∀ ℓ, 0 < n ℓ) (CW : ℝ≥0)
    (W : Ω → ℕ → ℕ → ℕ → ℝ) (hW : IsLinearNetInit P n CW W) (x : ℕ → ℝ)
    (ℓ i₁ i₂ i₃ i₄ : ℕ) (hℓ : 1 ≤ ℓ)
    (hi₁ : i₁ < n ℓ) (hi₂ : i₂ < n ℓ) (hi₃ : i₃ < n ℓ) (hi₄ : i₄ < n ℓ) :
    ∫ ω, linearPreact n (W ω) x ℓ i₁ * linearPreact n (W ω) x ℓ i₂ *
        linearPreact n (W ω) x ℓ i₃ * linearPreact n (W ω) x ℓ i₄ ∂P
      = wickDelta4 i₁ i₂ i₃ i₄ *
          ((CW : ℝ) ^ (2 * ℓ) * (∏ ℓ' ∈ Finset.Ico 1 ℓ, (1 + 2 / (n ℓ' : ℝ))) *
            inputKernel (n 0) x x ^ 2) := by sorry

end DeepLearningTheory
