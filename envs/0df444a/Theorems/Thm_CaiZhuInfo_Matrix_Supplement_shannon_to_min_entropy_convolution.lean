-- Prove2me | Theorems.Thm_CaiZhuInfo_Matrix_Supplement_shannon_to_min_entropy_convolution
-- name    : CaiZhuInfo.Matrix.Supplement.shannon_to_min_entropy_convolution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:04:06.344409+00:00
-- url     : https://prove2.me/theorems/3c6aa380-2c5a-4c0e-bca4-535fec1ec16d
-- title:
--   Theorem 1.1 — Shannon-to-min-entropy convolution bound
-- statement:
--   Let $G$ be an arbitrary group, written multiplicatively (discrete; it may be infinite or noncommutative). Let $k\ge1$ and let $Q_1,\dots,Q_k$ be finitely supported probability distributions on $G$, not necessarily identical. Let $Z_1,\dots,Z_k$ be independent with $Z_i\sim Q_i$; the convolution $Q_1*\cdots*Q_k$ is the law of the ordered product $Z_1Z_2\cdots Z_k$. Write $\|P\|_\infty=\max_g P(g)=2^{-H_\infty(P)}$ for the largest point probability, and $H(Q_i)=\sum_{x:\,Q_i(x)>0}Q_i(x)\log_2\frac1{Q_i(x)}$ for the Shannon entropy in bits. Define
--
--   $$s=\max_{1\le i\le k}|\operatorname{supp}Q_i|,\qquad n=\lfloor\log_2 s\rfloor,\qquad H=\frac1k\sum_{i=1}^k H(Q_i),$$
--
--   and assume $s\ge2$. Then
--
--   $$\|Q_1*\cdots*Q_k\|_\infty\le C_0\,\exp\big((n\ln2-k)^+\big)\,2^{-H},\qquad C_0=16+8\sqrt2,$$
--
--   where $a^+=\max\{a,0\}$ and $\ln$ is the natural logarithm. Consequently, if $k\ge\lceil n\ln 2\rceil$, then
--
--   $$H_\infty(Q_1*\cdots*Q_k)\ge H-c_0,\qquad c_0=\log_2C_0.$$
--
--   The loss $c_0$ does not depend on the group, the support sizes or the factor laws. This is the fixed-count, distinct-factor form of the entropy conversion; the mission's Corollary 4.4 is its Poisson-count, identical-factor sibling.
--
--   **Formalization Note** The factor laws are a family `Q : Fin k → PMF G` (index $i$ of the paper is `Fin` index $i-1$). The ordered convolution is the left fold of the published binary ordered convolution (law of $xy$ with $x$ from the left law), started at the point mass at the identity, so the product is $Z_1\cdots Z_k$ in this order. The largest point probability is the supremum of the point masses, which is a maximum because the product law is finitely supported; $H_\infty=-\log_2\|\cdot\|_\infty$.
--
--   Differences from the source:
--   - encoding: Q₁ ∗ ⋯ ∗ Q_k, the law of Z₁⋯Z_k → left fold of the binary ordered convolution over List.ofFn Q, starting from PMF.pure 1; reason: convolving with the point mass at the identity first changes nothing, and the fold keeps the paper's factor order
--   - encoding: ‖P‖∞ = max_g P(g) and H∞ = −log₂‖P‖∞ → largestPoint (sSup of the range of the real point masses) and −logb 2 of it; reason: the point masses lie in [0,1] and the product law has finite support, so the supremum is the attained maximum
--   - encoding: k ≥ ⌈n ln 2⌉ → Nat.ceil ((n : ℝ) * Real.log 2) ≤ k; reason: same condition with the real ceiling of a nonnegative number
-- source:
--   Xiaohong Cai, Mingyang Zhu, STOC 2027 submission #616 (October 2026), Theorem 1.1, (2), printed p.2 / PDF p.3; convolution conventions §3, printed p.10 / PDF p.11; proof §4.3, printed pp.13–14 / PDF pp.14–15; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/616.pdf

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_compoundPoissonPoint

open scoped ENNReal

namespace CaiZhuInfo.Matrix.Supplement

open CaiZhuInfo.Matrix

/-- Cai–Zhu, STOC 2027 submission #616, Theorem 1.1, printed p.2 / PDF p.3.
`Q : Fin k → PMF G` are the (not necessarily identical) factor laws on an arbitrary
group `G`. The convolution `Q₁ ∗ ⋯ ∗ Q_k` is the law of the ordered product
`Z₁ ⋯ Z_k`, written as the left fold of the published binary ordered `convolution`
starting from the point mass at `1`. `s` is the largest support size, `n = ⌊log₂ s⌋`,
`H` the average bit entropy. Both conclusions of the theorem are stated. -/
theorem shannon_to_min_entropy_convolution {G : Type} [Group G] (k : ℕ) (hk : 1 ≤ k)
    (Q : Fin k → PMF G) (hQ : ∀ i, (Q i).support.Finite)
    (hs : 2 ≤ Finset.univ.sup fun i => (hQ i).toFinset.card) :
    let P : PMF G := (List.ofFn Q).foldl convolution (PMF.pure 1)
    let s : ℕ := Finset.univ.sup fun i => (hQ i).toFinset.card
    let n : ℕ := Nat.log2 s
    let H : ℝ := (1 / (k : ℝ)) * ∑ i, supportedEntropy (Q i) (hQ i)
    largestPoint (mass P) ≤
        C₀ * Real.exp (max ((n : ℝ) * Real.log 2 - k) 0) * (2 : ℝ) ^ (-H) ∧
      (Nat.ceil ((n : ℝ) * Real.log 2) ≤ k →
        H - c₀ ≤ -logTwo (largestPoint (mass P))) := by sorry

end CaiZhuInfo.Matrix.Supplement
