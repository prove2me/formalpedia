-- Prove2me | Theorems.Thm_CombOpt_SpanningTree_edge_mem_circuit_iff
-- name    : CombOpt.SpanningTree.edge_mem_circuit_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:04:31.11158+00:00
-- url     : https://prove2.me/theorems/0a78a92f-8a47-4c5d-bb69-00d645ee0f30
-- title:
--   Lemma 2.1 — an edge lies on a circuit iff its ends are joined in $G\setminus e$
-- statement:
--   Let $G$ be a graph and $e$ an edge of $G$ with ends $u$ and $v$ (possibly a loop, $u=v$). Then $e$ is an edge of some circuit of $G$ if and only if there is a path from $u$ to $v$ in $G\setminus e$, the graph obtained from $G$ by deleting $e$.
--
--   It follows that deleting an edge of a circuit from a connected graph leaves it connected; the lemma underlies the correctness of the greedy MST algorithms.
--
--   **Formalization Note** $G\setminus e$ has the same nodes and the edges $E\setminus\{e\}$ with the same ends, so a path in $G\setminus e$ is a path of $G$ whose edge list does not contain $e$.
--
--   Differences from the source:
--   - encoding: a path in G\e from u to v → a path of G from u to v whose edge list does not contain e; reason: G\e has the nodes of G and the edges E\{e} with the same ends (p. 10), so these are the same paths
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Lemma 2.1, p. 11 (PDF p. 20)

import Mathlib
import Definitions.Def_CombOpt_SpanningTree_Graph_IsCircuit

namespace CombOpt.SpanningTree

/-- **Lemma 2.1: an edge lies on a circuit iff its ends are joined by a path avoiding it.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Lemma 2.1, p. 11 (PDF p. 20): "An edge e = uv of G is an edge of a circuit of G if and only
if there is a path in G\e from u to v."

For an edge `e` with ends `u, v`: there is a circuit of `G` having `e` among its edges if and only
if there is a path from `u` to `v` that does not use `e`.

**Formalization Note.** `G\e` has the same nodes and the edges `E \ {e}` with the same ends
(p. 10), so its paths are the paths of `G` not using `e`. Loops and parallel edges are allowed;
for a loop `e` at `u` both sides hold (the loop is a circuit of length 1; the one-node path `u`
avoids `e`). -/
theorem edge_mem_circuit_iff {V E : Type*} [Fintype V] [Fintype E] (G : Graph V E) (e : E)
    (u v : V) (he : G.ends e = s(u, v)) :
    (∃ (w : V) (p : G.Walk w w), G.IsCircuit p ∧ e ∈ p.edges) ↔
      ∃ p : G.Walk u v, e ∉ p.edges := by sorry

end CombOpt.SpanningTree
