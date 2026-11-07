-- Prove2me | Theorems.Thm_DisjointPathsDAG_theorem_4_7_reduction
-- name    : DisjointPathsDAG.theorem_4_7_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:30:33.806394+00:00
-- url     : https://prove2.me/theorems/f9fd1f8d-0acb-4260-adee-ec45ca82743d
-- title:
--   Proof of Theorem 4.7 — lightest copies, tight graphs, and the field size
-- statement:
--   Let $G$ be a DAG with $n$ vertices, $m$ edges, real edge weights (of any sign) and $k\ge3$ terminal pairs.
--
--   1. Keeping one lightest copy of every class of parallel edges leaves fewer than $n^2$ edges; every k-DSP solution of the reduced graph is one of $G$, and the instance is feasible if and only if the reduced one is.
--   2. For a source $s$ with $d(v)=\mathrm{dist}_G(s,v)$, let $H_s$ consist of the edges $(u,v)$ with $d(u)<+\infty$ and $d(v)=d(u)+w(u,v)$. Then the $s$–$t$ paths in $H_s$ are exactly the shortest $s$–$t$ paths of $G$; hence the k-DSP solutions of $G$ are exactly the disjoint-paths solutions in $(H_{s_1},\dots,H_{s_k})$.
--   3. For every $c>0$, with $q=\lceil\log_2(2k)\rceil+\lceil(c+1)\log_2(n+1)\rceil$,
--   $$2k\le 2^q,\qquad \frac{n}{2^q}\le n^{-c}\quad(n\ge1),$$
--   and $q\le D\lceil\log_2(n+2)\rceil$ for a constant $D$ depending on $k$ and $c$.
--
--   These are the reductions from k-DSP to the setting of Theorem 4.1 and the choice of the field.
--
--   Differences from the source:
--   - encoding: the graph after keeping one lightest copy → the edge subgraph `lightestCopies G wt` (ties broken by the smaller index); reason: same graph
--   - encoding: $d_i(v)=\mathrm{dist}_G(s_i,v)$, $+\infty$ if unreachable → `dist` in `WithTop ℝ`; reason: the least weight of a path, $\top$ if none
--   - encoding: "field elements fit in O(log n)-bit words for fixed k and c" → $q\le D\lceil\log_2(n+2)\rceil$; reason: the number of bits of a field element
-- source:
--   Cao–Qi–Wang, Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths, arXiv:2611.02154 (held version, sha256 2d2202de…7e17), proof of Theorem 4.7, p.22

import Mathlib
import Definitions.Def_DisjointPathsDAG_Graph

set_option autoImplicit false

namespace DisjointPathsDAG

/-- Cao–Qi–Wang, *Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths*,
arXiv:2611.02154 (held version, sha256 2d2202de…7e17), proof of Theorem 4.7, p.22: "A shortest path
through a parallel class can use a lightest copy, so feasibility is unchanged, and afterwards m < n2. For
k-DSP, compute di(v) := distG(si, v) by topological dynamic programming with O(k(m + n)) exact
operations, and let Hi consist of the edges (u, v) with di(u) < +∞ and di(v) = di(u) + w(u, v). Along a
path of Hi from si to ti the labels telescope to length di(ti), and every edge of a shortest si–ti path is
tight because its prefixes are shortest; hence the si–ti paths in Hi are exactly the shortest ones."
and "Use F := F2q with q := ⌈log2(2k)⌉ + ⌈(c + 1) log2(n + 1)⌉, so that |F| ≥ 2k, n/|F| ≤ n−c, and field
elements fit in O(log n)-bit words for fixed k and c."

Let `G` be a DAG with real edge weights `wt` (negative weights allowed) and `k ≥ 3` terminal pairs.
1. Keeping one lightest copy of every parallel class leaves fewer than `n²` edges, every k-DSP
   solution of the reduced graph is one of `G`, and feasibility is unchanged.
2. For every source `s`, a list of edges is an `s`–`t` path of the tight graph of `s` iff it is a
   shortest `s`–`t` path of `G`; hence the k-DSP solutions of `G` are exactly the disjoint-paths
   solutions in the tight graphs `H₁, …, H_k` of the sources.
3. For every `c > 0`, with `q(n) := ⌈log₂(2k)⌉ + ⌈(c + 1) log₂(n + 1)⌉`: `2k ≤ 2^q(n)` and
   `n / 2^q(n) ≤ n^(−c)` for every `n ≥ 1`, and `q(n) ≤ D · ⌈log₂(n + 2)⌉` for a constant `D`.

**Formalization Note** The reduced graph is the edge-subgraph `lightestCopies G wt` of `G` (ties broken
by the smaller index); its k-DSP solutions are those of `IsDSPSolutionIn` for that edge set. Distances
take values in `WithTop ℝ` (`⊤` for an unreachable vertex). The running-time remarks of the passage
belong to the goal. -/
theorem theorem_4_7_reduction {n m k : ℕ} (hk : 3 ≤ k) (G : Digraph n m) (wt : Fin m → ℝ)
    (pairs : Fin k → Fin n × Fin n) (hG : G.IsAcyclic) :
    ((lightestCopies G wt).card < n ^ 2 ∧
      (∀ P, IsDSPSolutionIn G (lightestCopies G wt) wt pairs P → IsDSPSolution G wt pairs P) ∧
      (DSPFeasible G wt pairs ↔ DSPFeasibleIn G (lightestCopies G wt) wt pairs)) ∧
    ((∀ (s t : Fin n) (p : List (Fin m)),
        G.IsPath (tightEdges G wt s) s t p ↔ G.IsShortestIn Finset.univ wt s t p) ∧
      (∀ P : Fin k → List (Fin m), IsDSPSolution G wt pairs P ↔
        G.IsSolutionIn (fun i => tightEdges G wt (pairs i).1) pairs P)) ∧
    (∀ c : ℝ, 0 < c →
      (∀ n' : ℕ, 1 ≤ n' →
        2 * k ≤ 2 ^ (⌈Real.logb 2 (2 * k)⌉₊ + ⌈(c + 1) * Real.logb 2 (n' + 1)⌉₊) ∧
        (n' : ℝ) / 2 ^ (⌈Real.logb 2 (2 * k)⌉₊ + ⌈(c + 1) * Real.logb 2 (n' + 1)⌉₊) ≤
          (n' : ℝ) ^ (-c)) ∧
      ∃ D : ℕ, ∀ n' : ℕ, ⌈Real.logb 2 (2 * k)⌉₊ + ⌈(c + 1) * Real.logb 2 (n' + 1)⌉₊ ≤
        D * Nat.clog 2 (n' + 2)) := by sorry

end DisjointPathsDAG
