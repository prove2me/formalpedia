-- Prove2me | Theorems.Thm_CSPSubsample_claim_A_1
-- name    : CSPSubsample.claim_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:14:10.123724+00:00
-- url     : https://prove2.me/theorems/29e753d7-c76a-46d9-b816-44dc09d81be8
-- title:
--   Claim A.1 — $1-k^2/N\le N^{\underline k}/N^k\le 1$
-- statement:
--   For integers $1\le k\le N$, with $N^{\underline k}=N(N-1)\cdots(N-k+1)$ the falling factorial,
--   $$
--   1-\frac{k^2}{N}\ \le\ \frac{N^{\underline k}}{N^k}\ \le\ 1 .
--   $$
--   It measures the gap between the two normalizations of the paper (the number of distinct-variable tuples versus the power $N^k$) and enters the bias bound (Lemma 4.4) and the lower half of the subsampling theorem.
--
--   Differences from the source: none.
-- source:
--   Bernasconi, Castiglioni, Celli, Farina, Malavolta, A Subsampling Theorem for Constraint Satisfaction Problems with Large Arity, arXiv:2608.00203 (PDF sha256 fd9ae01113266fee273c46c14c8a1a39f36a958dba3fc276cd74bf4c3daff445), Claim A.1, p.26 (PDF p.28)

import Mathlib

set_option autoImplicit false

namespace CSPSubsample

/-- **Claim A.1** (arXiv:2608.00203 (PDF sha256 fd9ae011…), p.26 = PDF p.28). For integers
`1 ≤ k ≤ N`, `1 − k²/N ≤ N^{\underline k}/N^k ≤ 1`.

**Formalization Note** `N^{\underline k} = N(N−1)⋯(N−k+1)` is `Nat.descFactorial N k`; `N^k` is
the power. Both inequalities are stated. -/
theorem claim_A_1 (k N : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) :
    1 - (k : ℝ) ^ 2 / N ≤ (N.descFactorial k : ℝ) / (N : ℝ) ^ k ∧
      (N.descFactorial k : ℝ) / (N : ℝ) ^ k ≤ 1 := by sorry

end CSPSubsample
