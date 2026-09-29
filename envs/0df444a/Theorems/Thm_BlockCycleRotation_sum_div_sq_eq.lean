-- Prove2me | Theorems.Thm_BlockCycleRotation_sum_div_sq_eq
-- name    : BlockCycleRotation.sum_div_sq_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:58:20.385494+00:00
-- url     : https://prove2.me/theorems/d3452f00-ce3b-4b62-971e-132d313edc53
-- title:
--   The main terms sum to $C n^2 \sum_{d\mid n} d^{-2}$
-- statement:
--   For $n>0$ and any constant $K$,
--   $$\sum_{d \mid n} K \left(\frac{n}{d}\right)^{2} = K\,n^2 \sum_{d\mid n} \frac{1}{d^{2}} .$$
--
--   The reindexing that collects the per-divisor main terms $K(n/d)^2$ into the closed form appearing in Lemma 19 and in the statement of Theorem 14.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemma 19. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Constant.lean#L441-L453

import Mathlib

open Real Finset

theorem BlockCycleRotation.sum_div_sq_eq {n : ℕ} (hn : 0 < n) (K : ℝ) :
    ∑ d ∈ n.divisors, K * (((n / d : ℕ) : ℝ)) ^ 2
      = K * (n : ℝ) ^ 2 * ∑ d ∈ n.divisors, 1 / (d : ℝ) ^ 2 := by sorry
