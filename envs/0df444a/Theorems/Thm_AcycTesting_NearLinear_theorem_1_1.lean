-- Prove2me | Theorems.Thm_AcycTesting_NearLinear_theorem_1_1
-- name    : AcycTesting.NearLinear.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:36:05.7442+00:00
-- url     : https://prove2.me/theorems/9245c3e0-0b7d-482c-9398-e9416e6dcceb
-- title:
--   Theorem 1.1 — every two-sided ε_η-tester for acyclicity of simple n-vertex digraphs with in- and outdegree ≤ d needs Ω(n^{1−η}) queries
-- statement:
--   For every fixed $\eta\in(0,1)$ there is a constant $\varepsilon_\eta>0$ such that for every integer $d\ge2$ there are constants $c>0$ and $n_0$ (which may depend on $\eta$ and $d$) with the following property. Let $n\ge n_0$, and let $\mathcal G(n,d)$ be the class of simple directed graphs on $[n]$ (no self-loops, no parallel edges) in which every indegree and every outdegree is at most $d$. Every randomized adaptive tester making at most $q$ queries that is a two-sided $\varepsilon_\eta$-tester for acyclicity on $\mathcal G(n,d)$ satisfies
--   $$c\,n^{1-\eta}\le q.$$
--   That is, it accepts every acyclic $G\in\mathcal G(n,d)$ with probability at least $2/3$ and rejects every $G\in\mathcal G(n,d)$ with $\mathrm{fas}(G)\ge\varepsilon_\eta dn$ with probability at least $2/3$. This holds both with **whole-vertex queries** (a query to $u$ returns the set of outneighbours of $u$) and with **indexed queries** (a query $(u,i)$, $i\in[d]$, returns the $i$-th outneighbour of $u$ in increasing ID order, or $\perp$).
--
--   The tester sees only outgoing edges; the indegree bound is an additional promise on the input. The distance $\varepsilon_\eta$ depends only on $\eta$, not on $d$ or $n$. The result rules out a tester with $O_{d,\varepsilon}(n^{\tau})$ queries for a common exponent $\tau<1$.
--
--   Differences from the source:
--   - encoding: vertex set [n] = {1, …, n}, vertex IDs → Fin n = {0, …, n − 1}, a vertex is its ID; reason: relabelling; the same graphs
--   - encoding: simple digraph (no self-loops, no parallel edges) → OutGraph (Fin n) (outneighbour Finsets, so at most one edge per ordered pair) with IsLoopless; reason: the representation excludes parallel edges; antiparallel pairs remain allowed, as in the source
--   - encoding: randomized adaptive tester making at most q queries → a PMF, independent of the input, on Boolean-output adaptive query trees of depth ≤ q (GraphIsoTesting.FixedGraph.RandomizedTester); accept = true, probabilities in ENNReal; reason: the published query model: worst-case cap on every run, repeated queries counted, unrestricted computation and randomness
--   - encoding: Ω(n^{1−η}) queries for every sufficiently large n → ∃ c > 0, ∃ n₀ (after d), ∀ n ≥ n₀, ∀ q, ∀ tester with cap q: c · (n : ℝ)^(1−η) ≤ q; reason: §1.1: ε_η depends only on η; the threshold (and, by the §3.1 convention for the reduction to a prescribed d, the hidden constant) may depend on η and d
--   - reading: Theorem 1.1 in the indexed model, with the remark of §1.1 and the end of §5.4 that it also holds with whole-vertex queries → both conjuncts: whole-vertex oracle (Finset answers) and indexed oracle (Fin n × Fin d → Option (Fin n)); reason: the paper states and proves the result for both query conventions
--   - encoding: indexed query (u, i), i ∈ {1, …, d}, answer the i-th outneighbour or ⊥; lists in increasing ID order (footnote 1) → i : Fin d (0-based), answer the entry at position i of the increasingly sorted outneighbour list, none for ⊥; reason: footnote 1 fixes the order; a tester only required to be correct on this representation is the most general indexed tester
-- source:
--   Czumaj, Peng, Wang, Near-Linear Lower Bounds for Testing Directed Acyclicity, arXiv:2611.04901v1 (sha256 5685fc7b…), p. 2 (PDF 5), Theorem 1.1

import Mathlib
import Definitions.Def_GraphIsoTesting_FixedGraph_QueryModel
import Definitions.Def_AcycTesting_NearLinear_Digraphs
import Definitions.Def_AcycTesting_NearLinear_Testers

open GraphIsoTesting.FixedGraph

namespace AcycTesting.NearLinear

/-- Theorem 1.1: for every `η ∈ (0,1)` there is `ε_η > 0` (chosen before `d`) such that for
every `d ≥ 2` there are `c > 0` and `n₀` with: for all `n ≥ n₀`, every randomized adaptive
two-sided `ε_η`-tester for acyclicity on `𝒢(n, d)` with at most `q` queries has
`c · n^{1-η} ≤ q`, both with whole-vertex queries and with indexed queries. -/
theorem theorem_1_1 :
    ∀ η : ℝ, 0 < η → η < 1 →
      ∃ ε : ℝ, 0 < ε ∧ ∀ d : ℕ, 2 ≤ d →
        ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ q : ℕ,
          (∀ T : RandomizedTester (Fin n) (Finset (Fin n)) q,
              IsTwoSidedTester wholeVertexOracle d ε T → c * (n : ℝ) ^ (1 - η) ≤ (q : ℝ)) ∧
          (∀ T : RandomizedTester (Fin n × Fin d) (Option (Fin n)) q,
              IsTwoSidedTester indexedOracle d ε T → c * (n : ℝ) ^ (1 - η) ≤ (q : ℝ)) := by sorry

end AcycTesting.NearLinear
