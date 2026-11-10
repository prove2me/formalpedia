-- Prove2me | Theorems.Thm_AssadiSemiStreaming_Greedy_lemma_6_4
-- name    : AssadiSemiStreaming.Greedy.lemma_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:40:54.342863+00:00
-- url     : https://prove2.me/theorems/98bd8f04-2e26-4965-81d2-0fb654239a3c
-- title:
--   Lemma 6.4 — Near equality of complementary-maximum buckets
-- statement:
--   Lemma 6.4. For all j ∈ [2m − 1] and t ∈ [L : D],
--   |R_{2m−j,t}| − 2⁻ᵐ · Cᴾ/D ⩽ |L_{j,t}| ⩽ |R_{2m−j,t}| + 2⁻ᵐ · Cᴾ/D.
--
--   For every m≥1 and 1≤j<2m, L≤t≤D, both real inequalities hold with the exact error 2^(−m) C^P/D. Bucket sizes count full labels, including unused coordinates.
--
--   Differences from the source:
--   - generalization: the construction section fixes a sufficiently large integer m → the construction claims hold for every integer m≥1; reason: the finite definitions and the proofs of these quantitative claims use only positivity of m; asymptotic conclusions still have their own thresholds
-- source:
--   Assadi, Jiang and Xiang (2026), Semi-Streaming Matching in a Single Pass II: Greedy is Optimal, supplied STOC 2027 submission manuscript (published basis per source.meta.json; SHA-256 8f66fdf7cb422cdd3accbae4cb24ebc61dd7ddb2e5e2d5422f4de6fc3f99395d), Lemma 6.4, printed p. 18 / PDF 20

import Definitions.Def_AssadiSemiStreaming_Greedy_DelayedWalk

namespace AssadiSemiStreaming.Greedy

theorem lemma_6_4 (m : ℕ) (hm : 1 ≤ m) (j t : ℕ)
    (hj : 1 ≤ j) (hjm : j < 2 * m) (ht : lengthBound m ≤ t) (htop : t ≤ delayBound m) :
    ((bucket m true (2 * m - j) t).card : ℝ) -
        (2 : ℝ) ^ (-(m : ℤ)) * (alphabetSize m : ℝ) ^ labelLength m / delayBound m ≤
      ((bucket m false j t).card : ℝ) ∧
    ((bucket m false j t).card : ℝ) ≤ ((bucket m true (2 * m - j) t).card : ℝ) +
        (2 : ℝ) ^ (-(m : ℤ)) * (alphabetSize m : ℝ) ^ labelLength m / delayBound m := by sorry

end AssadiSemiStreaming.Greedy
