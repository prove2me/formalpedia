-- Prove2me | Theorems.Thm_FastCLO_LowerBound_binomial_bound
-- name    : FastCLO.LowerBound.binomial_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:20:24.899809+00:00
-- url     : https://prove2.me/theorems/286c5dac-ec5f-4c86-8255-304a23c74fb4
-- title:
--   Proof of Theorem 3, pp. 21–22 — E|N¹ − N⁰| = Σₖ C(n,k)qᵏ(1−q)ⁿ⁻ᵏ E|2Bin(k,½) − k| ≤ √(nq)
-- statement:
--   Let $n \in \mathbb N$ and $0 \le q \le 1$. Suppose each of $n$ independent draws lands in a given cell with probability $q$, and each draw in the cell is labelled $1$ or $0$ with probability $1/2$ each. With $N^1, N^0$ the numbers of draws in the cell with label $1$ and $0$,
--   $$\mathbb E|N^1 - N^0| = \sum_{k=0}^n \binom nk q^k (1-q)^{n-k}\ \mathbb E\big|2\,\mathrm{Bin}(k,\tfrac12) - k\big| \;\le\; \sqrt{nq}.$$
--   Explicitly, the statement is
--   $$\sum_{k=0}^n \binom nk q^k (1-q)^{n-k} \sum_{j=0}^k \binom kj 2^{-k}\,|2j - k| \;\le\; \sqrt{nq}.$$
--
--   The page takes $q = 1/\eta$ (Theorem 3); the proof of Theorem 7 uses the same bound with $q = \zeta^\alpha/(\eta-1)$. Combined with the Jensen step it bounds the Bayes risk of every coordinate from below by $\tfrac12 ((1+\zeta)/(1-\zeta))^{-\sqrt{nq}}$.
--
--   **Formalization Note** The expectation is written as the page's explicit mixture over $k$ (the number of draws in the cell) and $j$ (the number of those labelled $1$).
-- source:
--   Hu, Kallus, Mao, Fast Rates for Contextual Linear Optimization, arXiv:2011.03030v3, proof of Theorem 3 (A.2), pp. 21–22, the display after "Thus, letting Bin(k, 1/2) …"; used with q = ζ^α/(η−1) in the proof of Theorem 7, p. 29

import Mathlib

namespace FastCLO.LowerBound

/-- The binomial bound (Hu, Kallus, Mao, arXiv:2011.03030v3, proof of Theorem 3, pp. 21–22): if each
of `n` draws lands in a cell with probability `q`, and each draw in the cell is labelled `1` or `0`
with probability `1/2`, then the expected absolute difference of the label counts satisfies
`E|N¹ − N⁰| = Σ_k C(n,k) q^k (1−q)^{n−k} E|2 Bin(k, 1/2) − k| ≤ √(nq)`.

Formalization Note: the expectation is written as the page's explicit mixture, with `k` the number of
draws in the cell and `j` the number of those labelled `1`. The page has `q = 1/η` (Theorem 3); the
proof of Theorem 7 uses `q = ζ^α/(η − 1)` (p. 29). -/
theorem binomial_bound (n : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k) *
        (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) / 2 ^ k * |2 * (j : ℝ) - k|) ≤
      Real.sqrt (n * q) := by sorry

end FastCLO.LowerBound
