-- Prove2me | Theorems.Thm_DeepLearningTheory_linearNet_connected_four_point
-- name    : DeepLearningTheory.linearNet_connected_four_point
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T21:47:23.171613+00:00
-- url     : https://prove2.me/theorems/56b0904a-5794-4e1a-8b18-194c38afd835
-- title:
--   Deep linear network: connected four-point correlator of two neurons (eq. 3.30)
-- statement:
--   For a zero-bias deep linear network with positive widths at initialization, a single input $x$, a layer $\ell\ge1$ and two distinct neurons $j\ne k$ of that layer,
--
--   $$\mathbb{E}\Big[\big(z^{(\ell)}_jz^{(\ell)}_j-G^{(\ell)}_2\big)\big(z^{(\ell)}_kz^{(\ell)}_k-G^{(\ell)}_2\big)\Big]=G^{(\ell)}_4-\big(G^{(\ell)}_2\big)^2,$$
--
--   where $G^{(\ell)}_2=C_W^{\ell}G^{(0)}_2$, $G^{(\ell)}_4=C_W^{2\ell}\prod_{\ell'=1}^{\ell-1}\big(1+\frac{2}{n_{\ell'}}\big)\big(G^{(0)}_2\big)^2$ and $G^{(0)}_2=\frac1{n_0}\sum_j x_j^2$. The nonzero right side measures the interaction between different neurons at finite width.
-- source:
--   Daniel A. Roberts and Sho Yaida (with Boris Hanin), *The Principles of Deep Learning Theory*, arXiv:2106.10165v2, https://arxiv.org/abs/2106.10165, §3.3, pp. 61–62, eqs. (3.25), (3.29), (3.30) (page numbers are the book's printed page numbers)

import Mathlib
import Definitions.Def_DLT_DeepLinearNetwork

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace DeepLearningTheory

theorem linearNet_connected_four_point {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (hn : ∀ ℓ, 0 < n ℓ) (CW : ℝ≥0)
    (W : Ω → ℕ → ℕ → ℕ → ℝ) (hW : IsLinearNetInit P n CW W) (x : ℕ → ℝ)
    (ℓ j k : ℕ) (hℓ : 1 ≤ ℓ) (hj : j < n ℓ) (hk : k < n ℓ) (hjk : j ≠ k) :
    ∫ ω, (linearPreact n (W ω) x ℓ j ^ 2 - (CW : ℝ) ^ ℓ * inputKernel (n 0) x x) *
        (linearPreact n (W ω) x ℓ k ^ 2 - (CW : ℝ) ^ ℓ * inputKernel (n 0) x x) ∂P
      = (CW : ℝ) ^ (2 * ℓ) * (∏ ℓ' ∈ Finset.Ico 1 ℓ, (1 + 2 / (n ℓ' : ℝ))) *
            inputKernel (n 0) x x ^ 2
          - ((CW : ℝ) ^ ℓ * inputKernel (n 0) x x) ^ 2 := by sorry

end DeepLearningTheory
