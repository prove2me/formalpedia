-- Prove2me | Theorems.Thm_AdWordsMSVV_Tradeoff_lemma_3_optimal_pair
-- name    : AdWordsMSVV.Tradeoff.lemma_3_optimal_pair
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:41.635841+00:00
-- url     : https://prove2.me/theorems/dcf17d8a-5e00-4b7e-bbab-8ef0a1460acc
-- title:
--   Proof of Lemma 3, pp. 8–9 — x* and y* are optimal for L and D, with common value N(1 − 1/k)^k
-- statement:
--   Let $k\ge1$ and $N\ge0$ be integers, and let $L$, $D$ be the factor-revealing LP of §4 and its dual. Put
--   $$x^*_i=\frac Nk\Bigl(1-\frac1k\Bigr)^{i-1},\qquad y^*_i=\frac1k\Bigl(1-\frac1k\Bigr)^{k-i-1}\qquad(1\le i\le k-1).$$
--   Then:
--   1. $x^*$ is feasible for $L$ and $y^*$ is feasible for $D$;
--   2. $c\cdot x^*=b\cdot y^*=N(1-1/k)^k$;
--   3. $c\cdot x\le c\cdot x^*$ for every feasible $x$ of $L$, and $b\cdot y^*\le b\cdot y$ for every feasible $y$ of $D$.
--
--   This is the explicit content of the proof of Lemma 3, and the source of the bound $b\cdot y^*\le N/e$ used in the proof of Theorem 8.
-- source:
--   Mehta, Saberi, Vazirani, Vazirani, AdWords and generalized on-line matching, J. ACM (2007), DOI 10.1145/1284320.1284321, pp. 8–9, proof of Lemma 3 (the two feasible solutions and the displayed value)

import Mathlib
import Definitions.Def_AdWordsMSVV_Tradeoff_LP

namespace AdWordsMSVV.Tradeoff
theorem lemma_3_optimal_pair (k N : ℕ) (hk : 1 ≤ k) :
    PrimalFeasible k N (xStar k N) ∧ DualFeasible k (yStar k) ∧
    primalObj k (xStar k N) = (N : ℝ) * (1 - 1 / (k : ℝ)) ^ k ∧
    dualObj k N (yStar k) = (N : ℝ) * (1 - 1 / (k : ℝ)) ^ k ∧
    (∀ x : ℕ → ℝ, PrimalFeasible k N x → primalObj k x ≤ primalObj k (xStar k N)) ∧
    (∀ y : ℕ → ℝ, DualFeasible k y → dualObj k N (yStar k) ≤ dualObj k N y) := by sorry
end AdWordsMSVV.Tradeoff
