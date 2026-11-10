-- Prove2me | Theorems.Thm_AssadiSemiStreaming_Greedy_prop_2_1_2
-- name    : AssadiSemiStreaming.Greedy.prop_2_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:39:23.703648+00:00
-- url     : https://prove2.me/theorems/7e5e5611-65d7-4bce-b1bb-400d70385999
-- title:
--   Proposition 2.1(2) — Joint absorption and maximum law
-- statement:
--   For a random walk W over [0 : 2m]:
--   2. For any 1 ⩽ s ⩽ j < 2m:
--   Pr_W(W ends in 0 ∧ w_max(W) = j | W starts at s) = s/(j · (j + 1)).
--
--   Here m≥1 and the starting state s and maximum j satisfy 1≤s≤j<2m. No finite walk horizon is imposed.
--
--   Differences from the source:
--   - encoding: walk time starts at one → first-passage trajectories start at time zero and count transitions; reason: shifting every time index by one preserves events and the number of transitions
--   - encoding: probabilities of the infinite-time joint event → nonnegative extended-real sums of disjoint first-absorption events; reason: all finite absorption times are included and divergence cannot acquire a zero default
-- source:
--   Assadi, Jiang and Xiang (2026), Semi-Streaming Matching in a Single Pass II: Greedy is Optimal, supplied STOC 2027 submission manuscript (published basis per source.meta.json; SHA-256 8f66fdf7cb422cdd3accbae4cb24ebc61dd7ddb2e5e2d5422f4de6fc3f99395d), Proposition 2.1(2), printed p. 3 / PDF 5

import Definitions.Def_AssadiSemiStreaming_Greedy_WalkLaws

namespace AssadiSemiStreaming.Greedy

theorem prop_2_1_2 (m : ℕ) (hm : 1 ≤ m) (s : Fin (2 * m + 1))
    (j : ℕ) (hs : 1 ≤ s.val) (hsj : s.val ≤ j) (hj : j < 2 * m) :
    zeroMaxProb m s j = ENNReal.ofReal ((s.val : ℝ) / ((j : ℝ) * (j + 1))) := by sorry

end AssadiSemiStreaming.Greedy
