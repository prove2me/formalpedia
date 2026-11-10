-- Prove2me | Theorems.Thm_AcycTesting_NearLinear_lemma_A_3
-- name    : AcycTesting.NearLinear.lemma_A_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:34:16.599242+00:00
-- url     : https://prove2.me/theorems/de335009-92cf-49b7-a161-7be9b260ebbb
-- title:
--   Lemma A.3 — a symmetric-mean (Maclaurin) inequality for a uniform s-subset
-- statement:
--   Let $z_1,\dots,z_N\ge0$ and let $I\subseteq[N]$ be a uniformly random subset of size $s$ ($0\le s\le N$). Then
--   $$\mathbb E\prod_{i\in I}z_i\ \le\ \Big(\frac1N\sum_{i=1}^N z_i\Big)^{s}.$$
--   Equivalently $e_s(z)\le\binom Ns\big(\frac1N\sum_i z_i\big)^s$ for the elementary symmetric polynomial $e_s$. It gives the exponential lower tail of balanced cuts (Lemma A.4).
--
--   Differences from the source:
--   - encoding: E over a uniform s-subset I ⊆ [N] → the average of ∏_{i∈I} z_i over Finset.powersetCard s (Fin N), i.e. the sum divided by choose N s, with s ≤ N; reason: a uniform s-subset exists exactly when s ≤ N; Fin N for [N]
-- source:
--   Czumaj, Peng, Wang, Near-Linear Lower Bounds for Testing Directed Acyclicity, arXiv:2611.04901v1 (sha256 5685fc7b…), p. 39 (PDF 42), Lemma A.3

import Mathlib

namespace AcycTesting.NearLinear

/-- Lemma A.3 (a symmetric-mean inequality): for `z₁, …, z_N ≥ 0` and a uniform `s`-subset
`I ⊆ [N]`, `E ∏_{i ∈ I} z_i ≤ ((1/N) ∑_i z_i)^s`. -/
theorem lemma_A_3 (N s : ℕ) (hs : s ≤ N) (z : Fin N → ℝ) (hz : ∀ i, 0 ≤ z i) :
    (∑ I ∈ (Finset.univ : Finset (Fin N)).powersetCard s, ∏ i ∈ I, z i) / (N.choose s : ℝ) ≤
      ((1 / (N : ℝ)) * ∑ i, z i) ^ s := by sorry

end AcycTesting.NearLinear
