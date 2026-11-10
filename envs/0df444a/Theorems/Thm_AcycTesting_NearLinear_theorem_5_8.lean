-- Prove2me | Theorems.Thm_AcycTesting_NearLinear_theorem_5_8
-- name    : AcycTesting.NearLinear.theorem_5_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:36:05.771849+00:00
-- url     : https://prove2.me/theorems/53b365e8-2802-4970-b623-ffe832d78a21
-- title:
--   Theorem 5.8 — at a degree d(η) and distance ε(η), every two-sided ε-tester for acyclicity needs at least n^{1−η} queries
-- statement:
--   For every fixed $\eta\in(0,1)$ there exist an integer $d\ge2$ and a constant $\varepsilon>0$ such that, for every sufficiently large $n$, every randomized adaptive two-sided $\varepsilon$-tester for directed acyclicity on $\mathcal G(n,d)$ makes at least $n^{1-\eta}$ queries. That is, if a law on adaptive query trees with at most $q$ whole-vertex queries accepts every acyclic $G\in\mathcal G(n,d)$ and rejects every $G\in\mathcal G(n,d)$ with $\mathrm{fas}(G)\ge\varepsilon dn$, each with probability at least $2/3$, then
--   $$n^{1-\eta}\le q.$$
--   Here $\mathcal G(n,d)$ is the class of simple digraphs on $[n]$ with every in- and outdegree at most $d$. This is the lower bound at a large degree depending on $\eta$; Lemma 5.9 and Lemma 5.10 transfer it to every fixed $d\ge2$.
--
--   Differences from the source:
--   - encoding: vertex set [n] = {1, …, n}, vertex IDs → Fin n = {0, …, n − 1}, a vertex is its ID; reason: relabelling; the same graphs
--   - encoding: simple digraph (no self-loops, no parallel edges) → OutGraph (Fin n) (outneighbour Finsets, so at most one edge per ordered pair) with IsLoopless; reason: the representation excludes parallel edges; antiparallel pairs remain allowed, as in the source
--   - encoding: randomized adaptive tester making at most q queries → a PMF, independent of the input, on Boolean-output adaptive query trees of depth ≤ q (GraphIsoTesting.FixedGraph.RandomizedTester); accept = true, probabilities in ENNReal; reason: the published query model: worst-case cap on every run, repeated queries counted, unrestricted computation and randomness
--   - encoding: queries of the model of §3.1 → whole-vertex queries (wholeVertexOracle: answer = the Finset of outneighbours); reason: §3.1 fixes whole-vertex queries as the model of Sections 3–5; the proof of Theorem 1.1 applies Lemma 5.9 "even with whole-vertex queries"
--   - encoding: requires at least n^{1−η} queries, for every sufficiently large n → ∃ n₀, ∀ n ≥ n₀, ∀ q, ∀ tester with cap q: (n : ℝ)^(1−η) ≤ q; reason: the meaning of "requires"; d and ε chosen before n
-- source:
--   Czumaj, Peng, Wang, Near-Linear Lower Bounds for Testing Directed Acyclicity, arXiv:2611.04901v1 (sha256 5685fc7b…), p. 21 (PDF 24), Theorem 5.8

import Mathlib
import Definitions.Def_GraphIsoTesting_FixedGraph_QueryModel
import Definitions.Def_AcycTesting_NearLinear_Digraphs
import Definitions.Def_AcycTesting_NearLinear_Testers

open GraphIsoTesting.FixedGraph

namespace AcycTesting.NearLinear

/-- Theorem 5.8 (degree depending on `η`), with whole-vertex queries. -/
theorem theorem_5_8 :
    ∀ η : ℝ, 0 < η → η < 1 →
      ∃ d : ℕ, 2 ≤ d ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ q : ℕ,
        ∀ T : RandomizedTester (Fin n) (Finset (Fin n)) q,
          IsTwoSidedTester wholeVertexOracle d ε T → (n : ℝ) ^ (1 - η) ≤ (q : ℝ) := by sorry

end AcycTesting.NearLinear
