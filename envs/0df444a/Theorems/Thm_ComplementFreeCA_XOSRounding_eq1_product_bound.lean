-- Prove2me | Theorems.Thm_ComplementFreeCA_XOSRounding_eq1_product_bound
-- name    : ComplementFreeCA.XOSRounding.eq1_product_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:25:09.364083+00:00
-- url     : https://prove2.me/theorems/3e10f441-6f08-45ca-b2a0-f7c9bee6d6f4
-- title:
--   Eq. (1): $1-\prod_{i\le k}(1-X_i)\ge(1-(1-1/n)^n)\sum_{i\le k}X_i$
-- statement:
--   Let $1\le k\le n$ and let $X_1,\dots,X_k\in[0,1]$ satisfy $X_1+\dots+X_k\le 1$. Then
--   $$1-\prod_{i=1}^k(1-X_i)\ \ge\ 1-\Big(1-\frac{\sum_{i=1}^kX_i}{k}\Big)^k\ \ge\ \Big(1-\Big(1-\frac1k\Big)^k\Big)\sum_{i=1}^kX_i\ \ge\ \Big(1-\Big(1-\frac1n\Big)^n\Big)\sum_{i=1}^kX_i .$$
--
--   This is the analytic core of Lemma 3.3: the probability that at least one of $k$ independent events with probabilities $X_i$ occurs is at least a $1-(1-1/n)^n\ (\ge 1-1/e)$ fraction of the sum of the probabilities.
--
--   **Formalization Note** The three inequalities of the chain are stated as a conjunction. In the paper the $X_i$ are the probabilities $X_i^j$ that bidder $i$ receives item $j$ in the preallocation, and $\sum_i X^j_i\le1$ comes from the item constraint of the LP.
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, pp. 7-8, §3.2, proof of Lemma 3.3, Eq. (1)

import Mathlib

namespace ComplementFreeCA.XOSRounding

theorem eq1_product_bound (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (X : Fin k → ℝ)
    (hX0 : ∀ i, 0 ≤ X i) (hX1 : ∀ i, X i ≤ 1) (hsum : ∑ i, X i ≤ 1) :
    1 - (1 - (∑ i, X i) / (k : ℝ)) ^ k ≤ 1 - ∏ i, (1 - X i) ∧
    (1 - (1 - 1 / (k : ℝ)) ^ k) * ∑ i, X i ≤ 1 - (1 - (∑ i, X i) / (k : ℝ)) ^ k ∧
    (1 - (1 - 1 / (n : ℝ)) ^ n) * ∑ i, X i ≤ (1 - (1 - 1 / (k : ℝ)) ^ k) * ∑ i, X i := by sorry

end ComplementFreeCA.XOSRounding
