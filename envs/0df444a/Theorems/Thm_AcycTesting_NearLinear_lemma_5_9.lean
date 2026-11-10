-- Prove2me | Theorems.Thm_AcycTesting_NearLinear_lemma_5_9
-- name    : AcycTesting.NearLinear.lemma_5_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:36:10.709906+00:00
-- url     : https://prove2.me/theorems/85bfd2c2-2473-4b46-b3cd-6623adcf0f81
-- title:
--   Lemma 5.9 — degree two: every two-sided δ_η-tester for acyclicity needs at least a_η n^{1−η} whole-vertex queries
-- statement:
--   For every fixed $\eta\in(0,1)$ there exist constants $\delta_\eta,a_\eta>0$ such that, for every sufficiently large $n$, every randomized adaptive two-sided $\delta_\eta$-tester for directed acyclicity on $\mathcal G(n,2)$ (simple digraphs on $[n]$ with every in- and outdegree at most $2$), even with whole-vertex queries, makes at least $a_\eta n^{1-\eta}$ queries:
--   $$a_\eta\,n^{1-\eta}\le q$$
--   for every law on adaptive trees with at most $q$ whole-vertex queries that accepts every acyclic $G\in\mathcal G(n,2)$ and rejects every $G\in\mathcal G(n,2)$ with $\mathrm{fas}(G)\ge2\delta_\eta n$, each with probability at least $2/3$.
--
--   Differences from the source:
--   - encoding: vertex set [n] = {1, …, n}, vertex IDs → Fin n = {0, …, n − 1}, a vertex is its ID; reason: relabelling; the same graphs
--   - encoding: simple digraph (no self-loops, no parallel edges) → OutGraph (Fin n) (outneighbour Finsets, so at most one edge per ordered pair) with IsLoopless; reason: the representation excludes parallel edges; antiparallel pairs remain allowed, as in the source
--   - encoding: randomized adaptive tester making at most q queries → a PMF, independent of the input, on Boolean-output adaptive query trees of depth ≤ q (GraphIsoTesting.FixedGraph.RandomizedTester); accept = true, probabilities in ENNReal; reason: the published query model: worst-case cap on every run, repeated queries counted, unrestricted computation and randomness
--   - encoding: requires at least a_η n^{1−η} queries, for every sufficiently large n → ∃ n₀, ∀ n ≥ n₀, ∀ q, ∀ tester with cap q: a · (n : ℝ)^(1−η) ≤ q; reason: the meaning of "requires"; δ and a chosen before n
-- source:
--   Czumaj, Peng, Wang, Near-Linear Lower Bounds for Testing Directed Acyclicity, arXiv:2611.04901v1 (sha256 5685fc7b…), p. 22 (PDF 25), Lemma 5.9

import Mathlib
import Definitions.Def_GraphIsoTesting_FixedGraph_QueryModel
import Definitions.Def_AcycTesting_NearLinear_Digraphs
import Definitions.Def_AcycTesting_NearLinear_Testers

open GraphIsoTesting.FixedGraph

namespace AcycTesting.NearLinear

/-- Lemma 5.9 (degree two), with whole-vertex queries. -/
theorem lemma_5_9 :
    ∀ η : ℝ, 0 < η → η < 1 →
      ∃ δ : ℝ, 0 < δ ∧ ∃ a : ℝ, 0 < a ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ q : ℕ,
        ∀ T : RandomizedTester (Fin n) (Finset (Fin n)) q,
          IsTwoSidedTester wholeVertexOracle 2 δ T → a * (n : ℝ) ^ (1 - η) ≤ (q : ℝ) := by sorry

end AcycTesting.NearLinear
