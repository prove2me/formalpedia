-- Prove2me | Theorems.Thm_ConstructiveArboricity_Exact_orientations_and_pseudoforests
-- name    : ConstructiveArboricity.Exact.orientations_and_pseudoforests
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:39:30.701685+00:00
-- url     : https://prove2.me/theorems/0afbd3aa-ec74-4429-abff-fa5c59717535
-- title:
--   Lemma 2.2 — Orientations and pseudoforests
-- statement:
--   Let $G$ be a finite simple undirected graph. For every integer $k\ge0$,
--
--   $$G\text{ has a }k\text{-out orientation}\quad\Longleftrightarrow\quad E(G)\text{ partitions into }k\text{ pseudoforests}.$$
--
--   Moreover, its pseudoarboricity satisfies
--
--   $$\rho(G)=\min_{\mathcal O}\max_{v\in V(G)}d^+_{\mathcal O}(v).$$
--
--   The minimum maximum outdegree is represented as the least feasible uniform outdegree bound, giving zero when there are no vertices. Each orientation directs every edge exactly once. The equivalence includes $k=0$, when either side can hold precisely for an edgeless graph. This identifies the parameter computed by orientation algorithms with pseudoarboricity.
--
--   Differences from the source:
--   - encoding: a finite simple undirected graph with its edge sets → vertices Fin n, edge identities Fin m, an injective unordered endpoint map, and color fibers; reason: every finite simple graph admits such labels; isolated vertices and empty color classes are retained
--   - encoding: minimum over orientations of their maximum vertex outdegree → least k admitting an orientation with every outdegree at most k; reason: equivalent finite optimization, with value zero on the empty graph
--   - encoding: a pseudoforest has at most one cycle in each connected component → the published counting predicate requires every finite vertex set to span at most its cardinality in undirected edges; reason: equivalent for finite simple graphs; the separate pseudoforest_component_bridge target explicitly relates this predicate to the component definition
-- source:
--   Gholami, Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani and Shahrezaei, Constructive Arboricity in Almost-Linear Time for Dense Graphs, STOC 2027 submission #1476 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1476.pdf, Lemma 2.2, p.8

import Mathlib
import Definitions.Def_ConstructiveArboricity_Exact_Graph

namespace ConstructiveArboricity.Exact

/-- Gholami et al., STOC 2027 submission #1476 (October 2026), Lemma 2.2,
p.8. PDF sha256 9aa896d448cf63b4f502235eca19f59eb0468fad89783d21467b281518e3c512.
Both directions, including k=0, and the minimum-maximum identity. -/
theorem orientations_and_pseudoforests (G : Graph) :
    (∀ k : ℕ, (∃ tail, G.IsKOut k tail) ↔
      ∃ c : Fin G.m → Fin k, G.PseudoforestPartition k c) ∧
    G.rho = G.minOutdegree := by sorry

end ConstructiveArboricity.Exact
