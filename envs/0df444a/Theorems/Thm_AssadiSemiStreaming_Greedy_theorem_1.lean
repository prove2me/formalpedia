-- Prove2me | Theorems.Thm_AssadiSemiStreaming_Greedy_theorem_1
-- name    : AssadiSemiStreaming.Greedy.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:40:12.107299+00:00
-- url     : https://prove2.me/theorems/89833e1a-4cfc-4a84-a15b-6ebfcf6bfa38
-- title:
--   Theorem 1 — No better-than-half single-pass semi-streaming matching
-- statement:
--   Theorem 1. There is no single-pass semi-streaming algorithm for the maximum matching problem that can achieve any constant approximation ratio strictly better than half with constant probability. The lower bound holds even on bipartite graphs that have a perfect matching.
--
--   For every algorithm family using eventual O(n polylog n) space, every fixed ε>0 and 0<q≤1, and every size threshold N, there is a positive even n≥N, a bipartite n-vertex graph with a perfect matching, and an edge order for which the probability of outputting a valid matching of size at least (1/2+ε)ν(G) is strictly less than q. Probability is over machine randomness, not the stream order. Computation is unrestricted, and deterministic machines are included.
--
--   Differences from the source:
--   - encoding: single-pass semi-streaming algorithms on finite graphs → families of stochastic finite-state machines on Fin n with s(n)≤B n(log₂(n+2))^k eventually; reason: all retained information is counted, time is unrestricted, fresh randomness is allowed, and every fixed space constant and exponent is quantified
--   - encoding: lower bound even on bipartite graphs with perfect matchings → bad instances have positive even vertex counts, with explicit bipartiteness and perfectness; reason: every nonempty perfect-matching instance has an even vertex count and the subclass also witnesses failure on general graphs
--   - encoding: no fixed better-than-half approximation with constant probability → for every positive ε and 0<q≤1, every semi-streaming family has arbitrarily large inputs with success probability strictly below q; reason: this is the negation of an eventual guarantee on every graph and order, including deterministic algorithms
-- source:
--   Assadi, Jiang and Xiang (2026), Semi-Streaming Matching in a Single Pass II: Greedy is Optimal, supplied STOC 2027 submission manuscript (published basis per source.meta.json; SHA-256 8f66fdf7cb422cdd3accbae4cb24ebc61dd7ddb2e5e2d5422f4de6fc3f99395d), Theorem 1, printed p. 1 / PDF 3; footnotes 6–7, printed p. 6 / PDF 8

import Definitions.Def_AssadiSemiStreaming_Greedy_MatchingStream

namespace AssadiSemiStreaming.Greedy

theorem theorem_1 (s : ℕ → ℕ) (A : (n : ℕ) → MatchingMachine n (s n))
    (hspace : SemiStreamingSpace s) (ε q : ℝ) (hε : 0 < ε) (hq : 0 < q) (hq1 : q ≤ 1) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ Even n ∧
      ∃ G : SimpleGraph (Fin n), ∃ stream : List (Sym2 (Fin n)),
        HardGraph G ∧ IsEdgeStream G stream ∧
        MatchingSuccess (A n) G stream (1 / 2 + ε) < ENNReal.ofReal q := by sorry

end AssadiSemiStreaming.Greedy
