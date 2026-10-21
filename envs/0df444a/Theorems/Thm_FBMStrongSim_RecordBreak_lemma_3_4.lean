-- Prove2me | Theorems.Thm_FBMStrongSim_RecordBreak_lemma_3_4
-- name    : FBMStrongSim.RecordBreak.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:01:34.852226+00:00
-- url     : https://prove2.me/theorems/8f84e74d-413c-4bac-b010-9da8f1d82e2d
-- title:
--   Lemma 3.4, p. 11 — the diagonal entries Var(c^k_j − b^k_j) of Σ^(k) are ≤ 2·2^{−2kH}
-- statement:
--   Let $B$ be a fractional Brownian motion on $[0,1]$ with Hurst index $H\in(0,1)$. For $k\ge1$ and $j=0,\dots,2^{k-1}-1$ put
--   $$c^k_j=\mathbb E\big[B(t^k_{2j+1})\,\big|\,B^H_{k-1}\big],\qquad b^k_j=\tfrac12\big(B(t^{k-1}_j)+B(t^{k-1}_{j+1})\big).$$
--   The covariance matrix $\Sigma^{(k)}$ of $c_k-b_k$ has diagonal entries $\operatorname{Var}(c^k_j-b^k_j)$, and these are uniformly bounded:
--   $$\operatorname{Var}\big(c^k_j-b^k_j\big)\le 2\cdot 2^{-2kH}.$$
--
--   This bounds the bias part of the midpoint displacement and feeds the second Borell–TIS step of Theorem 3.1.
--
--   **Formalization Note** The paper writes $\Sigma^{(k)}$ through the matrices $N_{k-1}$, $M_{k-1}$ and a generalized inverse (pp. 10–11) and states on p. 11 that its diagonal entries are the variances of $c^k_j-b^k_j$; the statement uses that description directly, with Mathlib's conditional expectation for $c^k_j$.
-- source:
--   Chen, Dong & Ni, ε-Strong simulation of fractional Brownian motion and related stochastic differential equations, arXiv:1902.07824v1, p. 11, Lemma 3.4 (proof: Appendix A.3, p. 39)

import Mathlib
import Definitions.Def_FBMStrongSim_RecordBreak_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FBMStrongSim.RecordBreak

/-- Lemma 3.4, p. 11: the diagonal entries of `Σ^(k)`, i.e. the variances of
`c^k_j − b^k_j` with `c^k_j = E[B^H(t^k_{2j+1}) | B^H_{k−1}]`, are at most `2 · 2^{−2kH}`. -/
theorem lemma_3_4 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {H : ℝ} (hH0 : 0 < H) (hH1 : H < 1) {B : ℝ → Ω → ℝ} (hB : IsFBM H B P)
    {k j : ℕ} (hk : 1 ≤ k) (hj : j < 2 ^ (k - 1)) :
    Var[fun ω => (P[B (dyadic k (2 * j + 1)) | levelSigma B (k - 1)]) ω
        - (B (dyadic (k - 1) j) ω + B (dyadic (k - 1) (j + 1)) ω) / 2; P]
      ≤ 2 * (2 : ℝ) ^ (-2 * (k : ℝ) * H) := by sorry

end FBMStrongSim.RecordBreak
