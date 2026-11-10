-- Prove2me | Theorems.Thm_AssadiSemiStreaming_Greedy_prop_2_1_3
-- name    : AssadiSemiStreaming.Greedy.prop_2_1_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:39:31.427276+00:00
-- url     : https://prove2.me/theorems/e0f184e0-fff7-4506-becb-1cb8d9f0f8cc
-- title:
--   Proposition 2.1(3) — Explicit absorption tail
-- statement:
--   For a random walk W over [0 : 2m]:
--   3. The probability that a random walk W starting from any state does not terminate within 16m³ steps is at most 2⁻ᵐ.
--
--   Here m≥1; the starting state may be either endpoint. Steps mean transitions, so the tail event excludes absorption through the indicated transition count.
--
--   Differences from the source:
--   - encoding: walk time starts at one → first-passage trajectories start at time zero and count transitions; reason: shifting every time index by one preserves events and the number of transitions
-- source:
--   Assadi, Jiang and Xiang (2026), Semi-Streaming Matching in a Single Pass II: Greedy is Optimal, supplied STOC 2027 submission manuscript (published basis per source.meta.json; SHA-256 8f66fdf7cb422cdd3accbae4cb24ebc61dd7ddb2e5e2d5422f4de6fc3f99395d), Proposition 2.1(3), printed p. 3 / PDF 5

import Definitions.Def_AssadiSemiStreaming_Greedy_WalkLaws

namespace AssadiSemiStreaming.Greedy

theorem prop_2_1_3 (m : ℕ) (hm : 1 ≤ m) (s : Fin (2 * m + 1)) :
    MarkovMixing.setAvoidTailProb (MarkovMixing.gamblersChain (2 * m)) s
      {0, Fin.last (2 * m)} (16 * m ^ 3) ≤ (2 : ℝ) ^ (-(m : ℤ)) := by sorry

end AssadiSemiStreaming.Greedy
