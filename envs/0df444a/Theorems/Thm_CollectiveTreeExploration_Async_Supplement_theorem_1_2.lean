-- Prove2me | Theorems.Thm_CollectiveTreeExploration_Async_Supplement_theorem_1_2
-- name    : CollectiveTreeExploration.Async.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:25:09.346621+00:00
-- url     : https://prove2.me/theorems/3b1ef917-ea72-4179-9115-8834d9d93ce1
-- title:
--   Theorem 1.2 — synchronous collective tree exploration in $2n/k+O(\log^2(k)D)$ rounds, $O(\log^2 k)$-competitive
-- statement:
--   There are universal constants $C>0$ and $K>0$ such that for every number of agents $k\ge2$ there exists a deterministic, legal, online synchronous collective tree exploration algorithm $A_k$ with unrestricted communication (in every round each of the $k$ agents traverses one edge) with the following two properties for **every** finite rooted tree $T$ with $n$ vertices and depth $D$:
--
--   1. (Round bound) its completion time satisfies
--   $$R(A_k,T)\;\le\;\frac{2n}{k}+C\,\log^2(k)\,D ;$$
--   2. (Competitiveness) the same algorithm is $O(\log^2 k)$-competitive:
--   $$R(A_k,T)\;\le\;K\,\log^2(k)\;\mathrm{OPT}_k(T),$$
--   where $\mathrm{OPT}_k(T)$ is the least number of rounds in which $k$ agents that know $T$ can visit all its vertices.
--
--   Here $\log$ is the natural logarithm, $2n/k$ is real division, and $C,K$ do not depend on $k$, $T$, $n$ or $D$. In particular $A_k$ explores every tree in finitely many rounds.
--
--   This is the synchronous counterpart of the paper's main asynchronous result (Theorem 1.1): the paper obtains it from Theorem 1.1 through the standard reduction in which the synchronous model corresponds to cyclic activation $1,2,\dots,k,1,2,\dots$, $k$ moves per round. It improves the previous best competitive ratio $O(\sqrt k)$ exponentially.
--
--   **Formalization Note** The completion time and $\mathrm{OPT}_k(T)$ take values in $\mathbb N\cup\{\infty\}$ and the bounds are compared in $[0,\infty]$; the first bound forces the completion time to be finite.
--
--   Differences from the source:
--   - encoding: "2n/k + O(log²(k)D) rounds" and "O(log²(k))-competitive" → explicit universal constants C > 0 and K > 0, chosen before k and the tree; reason: the O-terms hide universal constants.
--   - reading: synchronous model, identified by the paper with cyclic activation 1,…,k (agent i's move may use what agents 1,…,i−1 revealed earlier in the same round) → the classical simultaneous model of [FGKP06]: all k moves of a round are chosen from the history of the completed rounds; reason: Theorem 1.2 is stated for the classical synchronous problem of [FGKP06], in which all agents perform one move per round; every simultaneous algorithm is also a cyclic-activation algorithm, so this is not the weaker reading.
--   - reading: OPT(T), "the number of time steps required by any team of k agents to go through all edges of a tree T" (p.3) → least number of rounds in which k agents with full knowledge of T, each traversing an edge every round, visit every vertex; reason: in a tree every vertex is visited exactly when every edge has been traversed, and idle steps can be replaced by back-and-forth moves.
--   - reading: competitive ratio c(k), defined on p.3 by "at most c(k)(n/k + D) synchronous rounds" → R(A_k,T) ≤ K log²(k) OPT_k(T); reason: p.3 motivates the measure by OPT(T) = Θ(n/k + D); for trees with at least two vertices OPT_k(T) ≥ D and k·OPT_k(T) ≥ n − 1 (and OPT_k(T) ≤ O(n/k + D)), so the two forms agree up to a universal factor, and on the one-vertex tree both force 0 rounds, which every algorithm achieves.
-- source:
--   Romain Cosson, Laurent Massoulié, Polylogarithmic Collective Tree Exploration, STOC 2027 submission

import Mathlib
import Definitions.Def_CollectiveTreeExploration_Async_Supplement_Synchronous

namespace CollectiveTreeExploration.Async.Supplement

open CollectiveTreeExploration.Async

open scoped BigOperators ENNReal

/-- **Theorem 1.2** (Cosson–Massoulié, p.2). There are universal constants `C, K > 0` such that
for every `k ≥ 2` some deterministic online synchronous exploration algorithm for `k` agents with
unrestricted communication explores every finite rooted tree `T` with `n` vertices and depth `D`
in at most `2n/k + C · log²(k) · D` rounds, and the same algorithm is `O(log² k)`-competitive:
its number of rounds is at most `K · log²(k) · OPT_k(T)`. -/
theorem theorem_1_2 :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, 0 < K ∧ ∀ k : ℕ, 2 ≤ k → ∃ A : SyncAlgorithm k,
      LegalSyncExploration A ∧ ∀ T : ExpTree,
        ((roundsToExplore A T : ℕ∞) : ℝ≥0∞) ≤
            ENNReal.ofReal (2 * (T.size : ℝ) / (k : ℝ) + C * (Real.log k ^ 2 * (T.depth : ℝ))) ∧
        ((roundsToExplore A T : ℕ∞) : ℝ≥0∞) ≤
            ENNReal.ofReal (K * Real.log k ^ 2) * ((offlineOpt T k : ℕ∞) : ℝ≥0∞) := by sorry

end CollectiveTreeExploration.Async.Supplement
