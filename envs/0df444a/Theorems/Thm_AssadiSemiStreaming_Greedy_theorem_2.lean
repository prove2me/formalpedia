-- Prove2me | Theorems.Thm_AssadiSemiStreaming_Greedy_theorem_2
-- name    : AssadiSemiStreaming.Greedy.theorem_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:40:00.718581+00:00
-- url     : https://prove2.me/theorems/432b0171-bb1c-4b67-8594-2d036910668b
-- title:
--   Theorem 2 — Blueprint framework transfers value to streaming lower bounds
-- statement:
--   Theorem 2 ([AJX26a]). Suppose G is a proper blueprint for some parameters P, C ⩾ 1 and define
--   α(G) := (2 − 2 · value(G))/(2 − value(G)).
--   Then, for any fixed δ ∈ (0, 1), and any sufficiently large n, as a function of G, δ, the following holds. Any single-pass semi-streaming algorithm for maximum bipartite matching on n-vertex graphs cannot achieve an (α(G) + δ)-approximation with probability more than 1 − δ. The lower bound holds even on bipartite graphs that have a perfect matching.
--
--   For any proper blueprint, fixed δ∈(0,1), fixed B>0 and natural k, every sufficiently large n and every machine using at most B n(log₂(n+2))^k bits admit a bipartite graph, which has a perfect matching whenever n is even, and an edge order with success probability at most 1−δ at ratio α(G)+δ. The algorithm may output invalid edges, which count as failure. The theorem is independent of the constructed blueprint and is not a premise of Theorem 1.
--
--   Differences from the source:
--   - encoding: single-pass semi-streaming algorithms on finite graphs → families of stochastic finite-state machines on Fin n with s(n)≤B n(log₂(n+2))^k eventually; reason: all retained information is counted, time is unrestricted, fresh randomness is allowed, and every fixed space constant and exponent is quantified
--   - reading: any sufficiently large n, and the lower bound holds even on bipartite graphs that have a perfect matching → for every n ≥ N the bad instance is bipartite, and when n is even it also has a perfect matching; reason: no graph with an odd number of vertices has a perfect matching, so the perfect-matching clause is read as applying at even n; odd n keep the bipartite lower bound
--   - encoding: sufficiently large n as a function of the blueprint and δ, with semi-streaming space implicit → the threshold also depends on the fixed multiplicative space constant B and polylogarithmic exponent k; reason: the suppressed constants in O(n polylog n) must be fixed before n; no uniformity over unbounded space constants is claimed
-- source:
--   Assadi, Jiang and Xiang (2026), Semi-Streaming Matching in a Single Pass II: Greedy is Optimal, supplied STOC 2027 submission manuscript (published basis per source.meta.json; SHA-256 8f66fdf7cb422cdd3accbae4cb24ebc61dd7ddb2e5e2d5422f4de6fc3f99395d), Theorem 2, printed p. 6 / PDF 8

import Definitions.Def_AssadiSemiStreaming_Greedy_Blueprint
import Definitions.Def_AssadiSemiStreaming_Greedy_MatchingStream

namespace AssadiSemiStreaming.Greedy

theorem theorem_2 (G : Blueprint) (hG : G.Proper)
    (δ B : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (hB : 0 < B) (k : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ s : ℕ,
      (s : ℝ) ≤ B * n * (Real.log (n + 2) / Real.log 2) ^ k →
      ∀ A : MatchingMachine n s,
        ∃ H : SimpleGraph (Fin n), ∃ stream : List (Sym2 (Fin n)),
          (∃ color : Fin n → Bool, ∀ u v, H.Adj u v → color u ≠ color v) ∧
          (Even n → HardGraph H) ∧ IsEdgeStream H stream ∧
          MatchingSuccess A H stream (G.factor + δ) ≤ ENNReal.ofReal (1 - δ) := by sorry

end AssadiSemiStreaming.Greedy
