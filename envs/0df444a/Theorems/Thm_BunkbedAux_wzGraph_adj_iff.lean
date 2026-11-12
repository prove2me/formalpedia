-- Prove2me | Theorems.Thm_BunkbedAux_wzGraph_adj_iff
-- name    : BunkbedAux.wzGraph_adj_iff
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T01:33:16.242702+00:00
-- url     : https://prove2.me/theorems/fa15c18e-9110-4f58-90be-62632a4cdedd
-- title:
--   Adjacency in the Wierman--Ziff bunkbed graph
-- statement:
--   The graph realised by a Wierman--Ziff configuration $\psi$ on a bunkbed hypergraph is defined as the graph whose edge set is a union: over all pairs (hyperedge, level), the edges that the state at that pair contributes inside its triple, together with the vertical posts over the transversal set $T$. This lemma unfolds that definition into a usable adjacency criterion.
--
--   For vertices $u, v$ of the bunkbed $V \times \{0,1\}$,
--
--   $$u \sim v \iff \Bigl(\exists\, (i, l),\ \{u,v\} \in \mathrm{edges}\bigl(\psi(i,l),\, t_i,\, l\bigr)\Bigr) \ \text{ or } \ \bigl(u_1 = v_1 \ \wedge\ u_1 \in T \ \wedge\ u_2 \ne v_2\bigr),$$
--
--   together with $u \ne v$.
--
--   The second disjunct describes the posts: two vertices are joined by a post exactly when they share their underlying vertex, that vertex is transversal, and they sit on opposite levels. The first disjunct is deliberately left in terms of the state's edge set rather than expanded state by state, so that the criterion is uniform in the five Wierman--Ziff states.
--
--   The condition $u \ne v$ is retained because the construction passes through `fromEdgeSet`, which discards diagonal pairs; it cannot be dropped in general, since a hyperedge whose triple has a repeated vertex would otherwise contribute a loop.
--
--   **Mathematical role.** This is the basic tool for any argument that manipulates paths in the Wierman--Ziff bunkbed graph. In particular the involution argument for the robustness lemma proceeds by taking a path realising one connection event and transforming it into a path realising the other, reflecting the levels of the vertices lying beyond a distinguished hyperedge; checking that the transformed sequence is still a path is exactly a case analysis over this criterion, one case per edge type — post, hyperedge before the distinguished one, hyperedge after it, and the distinguished hyperedge itself.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Section 3.2 (p. 3), where the Wierman-Ziff bunkbed hypergraph percolation model is defined.

import Definitions.Def_BunkbedHypergraph
open Bunkbed Bunkbed.Hyper Finset SimpleGraph

namespace BunkbedAux

/-- **Adjacency in the Wierman-Ziff bunkbed graph.** Two vertices are adjacent exactly when some
hyperedge, on some level, contributes the edge joining them, or they are the two ends of a post
over the transversal set. -/
theorem wzGraph_adj_iff {V : Type*} [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ι → (V × V × V)) (T : Finset V) (ψ : ι × Fin 2 → WZ) (u v : V × Fin 2) :
    (wzGraph t T ψ).Adj u v ↔
      ((∃ p : ι × Fin 2, s(u, v) ∈ (ψ p).edges (t p.1) p.2)
        ∨ (u.1 = v.1 ∧ u.1 ∈ T ∧ u.2 ≠ v.2)) ∧ u ≠ v := by
  sorry

end BunkbedAux
