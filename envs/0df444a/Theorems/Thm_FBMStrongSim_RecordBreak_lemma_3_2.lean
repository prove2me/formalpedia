-- Prove2me | Theorems.Thm_FBMStrongSim_RecordBreak_lemma_3_2
-- name    : FBMStrongSim.RecordBreak.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:01:43.885605+00:00
-- url     : https://prove2.me/theorems/1727d3f9-055c-40a8-949d-d8a090ef442d
-- title:
--   Lemma 3.2, p. 9 — V_{k−1}(a^k_j) ≤ 2·2^{−2kH}
-- statement:
--   Let $B$ be a fractional Brownian motion on $[0,1]$ with Hurst index $H\in(0,1)$, and let $\mathbb V_{k-1}$ denote the conditional variance given the values $B^H_{k-1}=(B(t^{k-1}_0),\dots,B(t^{k-1}_{2^{k-1}}))$ on the grid $D_{k-1}$. For all $k\ge1$ and $j=0,1,\dots,2^{k-1}-1$, almost surely
--   $$\mathbb V_{k-1}\big(a^k_j\big)=\sigma^2_{kj}\le 2\cdot 2^{-2kH},\qquad a^k_j=B(t^k_{2j+1}).$$
--
--   This bounds the variance part of the midpoint displacement, uniformly in $j$, and feeds the Borell–TIS step of Theorem 3.1.
--
--   **Formalization Note** The conditional variance is Mathlib's `condVar`, $\mathbb E[(a-\mathbb E[a\mid\mathcal G])^2\mid\mathcal G]$ with $\mathcal G=\sigma(B^H_{k-1})$; it is defined almost everywhere, hence the "almost surely". For a Gaussian process it is a.s. the constant $\sigma^2_{kj}$ of the paper.
-- source:
--   Chen, Dong & Ni, ε-Strong simulation of fractional Brownian motion and related stochastic differential equations, arXiv:1902.07824v1, p. 9, Lemma 3.2 (proof: Appendix A.1, p. 38)

import Mathlib
import Definitions.Def_FBMStrongSim_RecordBreak_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FBMStrongSim.RecordBreak

/-- Lemma 3.2, p. 9: the conditional variance of `a^k_j = B^H(t^k_{2j+1})` given the values of
`B^H` on `D_{k−1}` is at most `2 · 2^{−2kH}`, for all `k ≥ 1` and `j = 0, …, 2^{k−1} − 1`. -/
theorem lemma_3_2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {H : ℝ} (hH0 : 0 < H) (hH1 : H < 1) {B : ℝ → Ω → ℝ} (hB : IsFBM H B P)
    {k j : ℕ} (hk : 1 ≤ k) (hj : j < 2 ^ (k - 1)) :
    ∀ᵐ ω ∂P, Var[B (dyadic k (2 * j + 1)); P | levelSigma B (k - 1)] ω
      ≤ 2 * (2 : ℝ) ^ (-2 * (k : ℝ) * H) := by sorry

end FBMStrongSim.RecordBreak
