-- Prove2me | Theorems.Thm_DeepLearningTheory_linearNet_mean_zero
-- name    : DeepLearningTheory.linearNet_mean_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T21:17:29.493184+00:00
-- url     : https://prove2.me/theorems/37ad29ea-a8bc-4325-a720-681bbdc8d428
-- title:
--   Deep linear network: vanishing mean preactivation (eq. 3.6)
-- statement:
--   Consider a zero-bias deep linear network with widths $n_0,n_1,\dots$ whose weights are initialized independently with $W^{(\ell)}_{ij}\sim\mathcal{N}(0, C_W/n_{\ell-1})$ (eq. 3.4). For every input $x$, every layer $\ell\ge1$ and every neuron $i$ in that layer,
--
--   $$\mathbb{E}\big[z^{(\ell)}_i(x)\big]=0.$$
-- source:
--   Daniel A. Roberts and Sho Yaida (with Boris Hanin), *The Principles of Deep Learning Theory*, arXiv:2106.10165v2, https://arxiv.org/abs/2106.10165, §3.1, pp. 55–56, eq. (3.6) (page numbers are the book's printed page numbers)

import Mathlib
import Definitions.Def_DLT_DeepLinearNetwork

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace DeepLearningTheory

theorem linearNet_mean_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (CW : ℝ≥0) (W : Ω → ℕ → ℕ → ℕ → ℝ)
    (hW : IsLinearNetInit P n CW W) (x : ℕ → ℝ) (ℓ i : ℕ) (hℓ : 1 ≤ ℓ) (hi : i < n ℓ) :
    ∫ ω, linearPreact n (W ω) x ℓ i ∂P = 0 := by sorry

end DeepLearningTheory
