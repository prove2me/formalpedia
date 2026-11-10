-- Prove2me | Theorems.Thm_AssadiSemiStreaming_Greedy_claim_5_2
-- name    : AssadiSemiStreaming.Greedy.claim_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:39:32.980205+00:00
-- url     : https://prove2.me/theorems/f7e0b58f-165b-497e-9c22-e5dbd1390381
-- title:
--   Claim 5.2 — Weighted partial sums of the specified starting distribution
-- statement:
--   Claim 5.2. For any j ∈ [m],
--   P_j := ∑_{s=1}^j µ(s) · s = γ_m · (j · (j + 1))/((2m − j) · (2m − j + 1)).
--
--   Here m≥1 and 1≤j≤m. P_j is the actual finite sum of the explicitly defined weights.
--
--   Differences from the source:
--   - encoding: real-valued weights given by rational formulas → rational weights cast to real numbers where probabilities are used; reason: all source weights are rational and the casts preserve the formulas exactly
-- source:
--   Assadi, Jiang and Xiang (2026), Semi-Streaming Matching in a Single Pass II: Greedy is Optimal, supplied STOC 2027 submission manuscript (published basis per source.meta.json; SHA-256 8f66fdf7cb422cdd3accbae4cb24ebc61dd7ddb2e5e2d5422f4de6fc3f99395d), Claim 5.2, printed p. 14 / PDF 16

import Definitions.Def_AssadiSemiStreaming_Greedy_WalkLaws

namespace AssadiSemiStreaming.Greedy

theorem claim_5_2 (m j : ℕ) (hm : 1 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) :
    (∑ s ∈ Finset.Icc 1 j, mu m s * s) =
    gamma m * ((j : ℚ) * (j + 1)) / (((2 * m : ℚ) - j) * ((2 * m : ℚ) - j + 1)) := by sorry

end AssadiSemiStreaming.Greedy
