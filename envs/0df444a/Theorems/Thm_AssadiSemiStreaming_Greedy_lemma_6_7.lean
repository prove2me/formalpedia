-- Prove2me | Theorems.Thm_AssadiSemiStreaming_Greedy_lemma_6_7
-- name    : AssadiSemiStreaming.Greedy.lemma_6_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:41:50.069387+00:00
-- url     : https://prove2.me/theorems/02cbc747-8fac-400a-8311-55a367268b47
-- title:
--   Lemma 6.7 — Exact quantitative value lower bound
-- statement:
--   Lemma 6.7. The value of blueprint G = G_m satisfies
--   value(G) ⩾ (1 − 1/m) · 2m/(3m + 1) − 3m · 2⁻ᵐ.
--
--   For every m≥1, the value is the actual number of constructed edges divided by C^P. The subtraction and negative power are real, with no truncation.
--
--   Differences from the source:
--   - generalization: the construction section fixes a sufficiently large integer m → the construction claims hold for every integer m≥1; reason: the finite definitions and the proofs of these quantitative claims use only positivity of m; asymptotic conclusions still have their own thresholds
--   - encoding: arbitrarily chosen minimum-size matchings between complementary buckets → zipped finite enumerations fix the subsets and their bijections, with C chosen as in Remark 6.2; reason: this is an explicit permitted construction, retains exactly the prescribed number of edges and types, and imposes no global properness condition
-- source:
--   Assadi, Jiang and Xiang (2026), Semi-Streaming Matching in a Single Pass II: Greedy is Optimal, supplied STOC 2027 submission manuscript (published basis per source.meta.json; SHA-256 8f66fdf7cb422cdd3accbae4cb24ebc61dd7ddb2e5e2d5422f4de6fc3f99395d), Lemma 6.7, printed p. 20 / PDF 22

import Definitions.Def_AssadiSemiStreaming_Greedy_Construction

namespace AssadiSemiStreaming.Greedy

theorem lemma_6_7 (m : ℕ) (hm : 1 ≤ m) :
    (1 - 1 / (m : ℝ)) * (2 * m : ℝ) / (3 * m + 1) -
      3 * m * (2 : ℝ) ^ (-(m : ℤ)) ≤ (constructedBlueprint m).value := by sorry

end AssadiSemiStreaming.Greedy
