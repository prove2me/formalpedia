-- Prove2me | Theorems.Thm_AssadiSemiStreaming_Greedy_claim_6_6
-- name    : AssadiSemiStreaming.Greedy.claim_6_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:41:45.742945+00:00
-- url     : https://prove2.me/theorems/eb3b055b-a6c2-4b73-9a77-61a82a57d8aa
-- title:
--   Claim 6.6 — Ban constraint for the constructed edge set
-- statement:
--   Claim 6.6 (“Ban constraint”). The edge-set E respects the ban constraint.
--
--   For every m≥1, every constructed edge and every common suffix satisfy the global ban condition of Definition 3.1. An isolated endpoint has no edge of any type.
--
--   Differences from the source:
--   - generalization: the construction section fixes a sufficiently large integer m → the construction claims hold for every integer m≥1; reason: the finite definitions and the proofs of these quantitative claims use only positivity of m; asymptotic conclusions still have their own thresholds
--   - encoding: arbitrarily chosen minimum-size matchings between complementary buckets → zipped finite enumerations fix the subsets and their bijections, with C chosen as in Remark 6.2; reason: this is an explicit permitted construction, retains exactly the prescribed number of edges and types, and imposes no global properness condition
-- source:
--   Assadi, Jiang and Xiang (2026), Semi-Streaming Matching in a Single Pass II: Greedy is Optimal, supplied STOC 2027 submission manuscript (published basis per source.meta.json; SHA-256 8f66fdf7cb422cdd3accbae4cb24ebc61dd7ddb2e5e2d5422f4de6fc3f99395d), Claim 6.6, printed p. 19 / PDF 21

import Definitions.Def_AssadiSemiStreaming_Greedy_Construction

namespace AssadiSemiStreaming.Greedy

theorem claim_6_6 (m : ℕ) (hm : 1 ≤ m) :
    (constructedBlueprint m).Ban := by sorry

end AssadiSemiStreaming.Greedy
