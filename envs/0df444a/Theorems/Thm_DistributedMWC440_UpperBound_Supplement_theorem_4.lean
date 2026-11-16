-- Prove2me | Theorems.Thm_DistributedMWC440_UpperBound_Supplement_theorem_4
-- name    : DistributedMWC440.UpperBound.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:53:08.380258+00:00
-- url     : https://prove2.me/theorems/06329ade-7e28-44c2-a72c-7c97758fe905
-- title:
--   Theorem 4 (Broadcast congested clique upper bound)
-- statement:
--   For every real number $k\ge1$, the $(k+1)$-Apx-MWC problem in undirected weighted graphs can be solved with high probability in
--
--   $$
--   \widetilde O\!\left(n^{1/k}\right)
--   $$
--
--   rounds in the broadcast congested clique model.
--
--   Precisely: for every weight exponent $q$, ID exponent $b$ and confidence exponent $c>0$ there are a message exponent $B$ and constants $C>0$, $p$, $n_0$ such that for every real $k\ge1$ some computable protocol, on every undirected input graph (not necessarily connected) with $n\ge\max(2,n_0)$ nodes, positive integer weights at most $n^q$ and distinct IDs below $\max(2,n)^b$, broadcasts only payloads below $\max(2,n)^B$, and with probability at least $1-n^{-c}$ halts within $C(\log n)^pn^{1/k}$ rounds with a correct output: every node knows the actual weight of one common simple cycle $C$ with $w(C)\le(k+1)\cdot\mathrm{OPT}$, and both endpoints of every edge know whether it lies on $C$; on a forest, the common no-cycle output.
--
--   Together with Theorem 5 this is tight up to polylogarithmic factors at integer $k\ge2$, conditional on the Erdős girth conjecture.
--
--   Differences from the source:
--   - reading: the broadcast congested clique model [DKO14] (initial knowledge not restated) → each node knows n, its ID and, for each incident edge, the neighbour's ID and the weight; broadcasts are received labelled with the sender's ID; reason: the standard clique convention; without neighbour IDs a node cannot identify its input edges at all
--   - encoding: an algorithm with unlimited local computation and O(log n)-bit broadcasts → a computable protocol, uniform in n, with independent private fair bits, whose broadcasts are below (max 2 n)^B on every execution; reason: the upper-bound class of the base mission, adapted to broadcasts; computability only restricts the algorithm
--   - encoding: Õ(·) bounds and 'with high probability' → for every confidence exponent, a message exponent B and constants C > 0, p, n₀ chosen before k and before the graph, with success probability ≥ 1 − n^(−confidence) for all n ≥ max 2 n₀; reason: spells out the uniform asymptotic statement as in the base mission's Theorem 1, for every real k ≥ 1 including k depending on n
--   - encoding: positive integer edge weights in n^(O(1)) → positive integer weights at most n^q for an arbitrary fixed weight exponent q; reason: the paper's standing assumption (printed p. 1), as in the base mission
--   - encoding: the minimum-cycle task where a cycle exists → OPT = ∞ on an acyclic input with an allowed no-cycle output; reason: totalizes the case the source leaves undefined, as in the base mission
-- source:
--   Yi-Jun Chang, Yanyu Chen, Dipan Dey, Yonggang Jiang, Gopinath Mishra, Hung Thuan Nguyen, Mingyang Yang, The Complexity of Distributed Minimum Weight Cycle Approximation, STOC 2027 submission #440 (October 2026), citation basis published; papers/stoc2027-440/source.pdf (SHA-256 cdee21a6e698b7d3caf34f1990ab2132af424195b394467946a89faadca70ac1), Theorem 4, printed p. 6 / PDF p. 8; restated and proved printed p. 30 / PDF p. 32; model printed p. 13 / PDF p. 15.

import Definitions.Def_DistributedMWC440_UpperBound_Supplement_BCC

open scoped ENNReal
open MeasureTheory
noncomputable section

namespace DistributedMWC440.UpperBound.Supplement

/-- Theorem 4 (Broadcast congested clique upper bound), Chang et al., STOC 2027 submission #440,
printed p. 6 / PDF p. 8 (restated and proved printed p. 30 / PDF p. 32): for every real `k ≥ 1`,
the `(k+1)`-Apx-MWC problem in undirected weighted graphs (positive integer weights at most `n^q`,
IDs below `(max 2 n)^b`) can be solved with high probability in `Õ(n^(1/k))` rounds of the
broadcast congested clique, with all constants uniform in `k`. -/
theorem theorem_4 (q b : ℕ) : BCCTradeoff q b := by sorry

end DistributedMWC440.UpperBound.Supplement
