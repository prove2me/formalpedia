-- Prove2me | Theorems.Thm_AssadiSemiStreaming_Greedy_claim_6_3
-- name    : AssadiSemiStreaming.Greedy.claim_6_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:40:37.307635+00:00
-- url     : https://prove2.me/theorems/7dc8e003-d454-4783-8f03-3eac7ec0492d
-- title:
--   Claim 6.3 — Reflection preserves bucket sizes
-- statement:
--   Claim 6.3. For all j ∈ [2m − 1] and t ∈ [D + L], |L_{j,t}| = |R_{j,t}|.
--
--   For every m≥1, use the concrete parameters and buckets of Definition 6.1 and Remark 6.2. The two walks share their starting law and delay; reflection reverses their steps.
--
--   Differences from the source:
--   - generalization: the construction section fixes a sufficiently large integer m → the construction claims hold for every integer m≥1; reason: the finite definitions and the proofs of these quantitative claims use only positivity of m; asymptotic conclusions still have their own thresholds
-- source:
--   Assadi, Jiang and Xiang (2026), Semi-Streaming Matching in a Single Pass II: Greedy is Optimal, supplied STOC 2027 submission manuscript (published basis per source.meta.json; SHA-256 8f66fdf7cb422cdd3accbae4cb24ebc61dd7ddb2e5e2d5422f4de6fc3f99395d), Claim 6.3, printed p. 17 / PDF 19

import Definitions.Def_AssadiSemiStreaming_Greedy_DelayedWalk

namespace AssadiSemiStreaming.Greedy

theorem claim_6_3 (m : ℕ) (hm : 1 ≤ m) (j t : ℕ)
    (hj : 1 ≤ j) (hjm : j < 2 * m) (ht : 1 ≤ t)
    (htop : t ≤ delayBound m + lengthBound m) :
    (bucket m false j t).card = (bucket m true j t).card := by sorry

end AssadiSemiStreaming.Greedy
