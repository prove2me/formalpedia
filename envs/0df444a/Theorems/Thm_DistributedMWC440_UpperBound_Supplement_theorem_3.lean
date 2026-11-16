-- Prove2me | Theorems.Thm_DistributedMWC440_UpperBound_Supplement_theorem_3
-- name    : DistributedMWC440.UpperBound.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:52:34.105623+00:00
-- url     : https://prove2.me/theorems/86273a23-c4fc-46d7-84eb-0b8d53d9a9e5
-- title:
--   Theorem 3 (Parallel computation)
-- statement:
--   For every real number $k\ge1$, the $(k+1)$-Apx-MWC problem in undirected weighted graphs can be solved with high probability using
--
--   $$
--   \widetilde O\!\left(m\,n^{1/k}\right)\ \text{work and}\ \widetilde O(1)\ \text{depth}
--   $$
--
--   in the randomized work-depth model.
--
--   Precisely: for every weight exponent $q$ and confidence exponent $c>0$ there are a word exponent $B$ and constants $C>0$, $p$, $n_0$ such that for every real $k\ge1$ some program, on every undirected simple graph with $n\ge\max(2,n_0)$ vertices, $m$ edges and positive integer weights at most $n^q$, halts with probability at least $1-n^{-c}$ with work at most $C(\log n)^p(m+1)n^{1/k}$, depth at most $C(\log n)^p$, and a correct output: a simple cycle $C$ with its actual weight $w(C)\le(k+1)\cdot\mathrm{OPT}$ and its edge-membership bits, or the no-cycle output on a forest.
--
--   This is a low-depth parallel algorithm with a continuous tradeoff between work and approximation ratio, for every real $k\ge1$.
--
--   Differences from the source:
--   - reading: the standard work-depth model [Ble96] with randomization → a fork-join shared-memory machine with finite program syntax, words of absolute value at most (max 2 n)^B, unit cost per statement, parallel loops charging the sum of work and the maximum of depth, concurrent reads, exclusive writes, and a read-only tape of independent fair bits; reason: the source does not fix the variant; variants differ by polylogarithmic factors, absorbed by Õ, and exclusive writes are the more restrictive choice
--   - encoding: Õ(m n^(1/k)) work and Õ(1) depth → work at most C (log n)^p (m + 1) n^(1/k) and depth at most C (log n)^p in one success event; reason: m + 1 differs from m only for edgeless graphs, where Õ(m n^(1/k)) = 0 is meaningless
--   - encoding: the graph as input and the cycle as output → edge list (u_i, v_i, w_i) in shared memory in arbitrary order and orientation; output flag, actual weight w(C) and one membership bit per edge in shared memory; reason: Definition 1.1's output in the centralized setting (printed p. 29)
--   - encoding: Õ(·) bounds and 'with high probability' → for every confidence exponent, a word exponent B and constants C > 0, p, n₀ chosen before k and before the graph, with success probability ≥ 1 − n^(−confidence) for all n ≥ max 2 n₀; reason: spells out the uniform asymptotic statement as in the base mission's Theorem 1, for every real k ≥ 1 including k depending on n
--   - encoding: positive integer edge weights in n^(O(1)) → positive integer weights at most n^q for an arbitrary fixed weight exponent q; reason: the paper's standing assumption (printed p. 1), as in the base mission
--   - encoding: the minimum-cycle task where a cycle exists → OPT = ∞ on an acyclic input with an allowed no-cycle output; reason: totalizes the case the source leaves undefined, as in the base mission
-- source:
--   Yi-Jun Chang, Yanyu Chen, Dipan Dey, Yonggang Jiang, Gopinath Mishra, Hung Thuan Nguyen, Mingyang Yang, The Complexity of Distributed Minimum Weight Cycle Approximation, STOC 2027 submission #440 (October 2026), citation basis published; papers/stoc2027-440/source.pdf (SHA-256 cdee21a6e698b7d3caf34f1990ab2132af424195b394467946a89faadca70ac1), Theorem 3, printed p. 5 / PDF p. 7; restated and proved printed p. 30 / PDF p. 32; model printed pp. 4–5 / PDF pp. 6–7.

import Definitions.Def_DistributedMWC440_UpperBound_Supplement_WorkDepth

open scoped ENNReal
open MeasureTheory
noncomputable section

namespace DistributedMWC440.UpperBound.Supplement

/-- Theorem 3 (Parallel computation), Chang et al., STOC 2027 submission #440, printed p. 5 /
PDF p. 7 (restated and proved printed p. 30 / PDF p. 32): for every real `k ≥ 1`, the
`(k+1)`-Apx-MWC problem in undirected weighted graphs (positive integer weights at most `n^q`)
can be solved with high probability using `Õ(m n^(1/k))` work and `Õ(1)` depth in the randomized
work-depth model, with all constants uniform in `k`. -/
theorem theorem_3 (q : ℕ) : WDTradeoff q := by sorry

end DistributedMWC440.UpperBound.Supplement
