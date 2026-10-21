-- Prove2me | Theorems.Thm_FlowsNetworks_Graphs_proper_cover_unrelated
-- name    : FlowsNetworks.Graphs.proper_cover_unrelated
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:41.174972+00:00
-- url     : https://prove2.me/theorems/40f5c53c-1d86-44b9-9ddf-fe9d379e5cf5
-- title:
--   Chapter II, Lemma 8.2 — proper covers give sets of mutually unrelated elements
-- statement:
--   Let $P = \{1, \dots, n\}$ be partially ordered by $\succ$ (irreflexive and transitive), and let $G = [S, T; \mathcal A]$ be the bipartite graph with nodes $S = \{x_1, \dots, x_n\}$, $T = \{y_1, \dots, y_n\}$ and arcs $(x_i, y_j)$ for $i \succ j$. A **cover** is a set $X \subseteq S \cup T$ containing an endpoint of every arc; it is **proper** if no proper subset of $X$ is a cover.
--
--   Corresponding to any proper cover $X \subseteq S \cup T$, there is a set $U \subseteq P$ of **mutually unrelated** elements (no two distinct members comparable under $\succ$) with
--   $$|X| + |U| = n.$$
--
--   Together with Lemma 8.1 and the König–Egerváry theorem it yields Dilworth's chain decomposition theorem.
--
--   **Formalization Note** $P$ is `Fin n`, $\succ$ a relation `r` with `IsStrictOrder`; the nodes of $G$ are `Fin n ⊕ Fin n` with `Sum.inl i` $= x_i$ and `Sum.inr j` $= y_j$, so $|X|$ counts nodes of both sides. "Proper" is read as "no proper subset is a cover" (every cover is a subset of itself).
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter II, p. 47, Lemma 8.2

import Mathlib
import Definitions.Def_FlowsNetworks_Graphs_PosetGraph

namespace FlowsNetworks.Graphs

/-- Ford–Fulkerson, *Flows in Networks*, Chapter II, Lemma 8.2 (p. 47). Let `P = {1, …, n}` be
partially ordered by `≻` (`r`, a strict partial order) and let `G = [S, T; 𝒜]` be the bipartite
graph with `(x_i, y_j) ∈ 𝒜` iff `i ≻ j`. Corresponding to any proper cover `X ⊆ S ∪ T`, there is a
set `U ⊆ P` of mutually unrelated elements with `|X| + |U| = n`. -/
theorem proper_cover_unrelated {n : ℕ} (r : Fin n → Fin n → Prop) [IsStrictOrder (Fin n) r]
    (X : Finset (Fin n ⊕ Fin n)) (hX : IsProperCover r X) :
    ∃ U : Finset (Fin n), MutuallyUnrelated r U ∧ X.card + U.card = n := by sorry

end FlowsNetworks.Graphs
