-- Prove2me | Theorems.Thm_CycleLengthsExp_ManyLengths_bfs_parent_tree
-- name    : CycleLengthsExp.ManyLengths.bfs_parent_tree
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-17T16:00:39.887756+00:00
-- url     : https://prove2.me/theorems/609fa623-081c-4031-a933-9db746531795
-- title:
--   Parent-choice tree / BFS tree (Friedman-Krivelevich p. 13): parent function one step closer to v0 -> acyclic spanning subgraph T on S preserving G-distances from v0
-- statement:
--   Parent-choice tree / BFS tree (Friedman–Krivelevich, p. 13, proof of Theorem 2:
--   "Run the BFS algorithm ... until a tree T ... is obtained").
--
--   Let G be a finite simple graph with decidable equality on vertices, S a set
--   of vertices containing v0, such that every vertex of S is reachable from v0
--   in G, and every non-root vertex v of S has a parent u in S with u adjacent
--   to v in G and dist_G(v0, u) + 1 = dist_G(v0, v) (one G-step closer to v0).
--   Then there is a subgraph T of G with vertex set exactly S, such that T is
--   acyclic, every vertex of S is reachable from v0 in T, and T preserves
--   G-distances from v0: dist_T(v0, v) = dist_G(v0, v) for all v in S.
--
--   Why: choose the parent function by choice; T's edges are the parent edges
--   (symmetrized). The parent chain from any v in S back to v0 is a T-walk of
--   length dist_G(v0, v), so dist_T <= dist_G; every T-edge is a G-edge, so
--   dist_G <= dist_T. Acyclicity follows because along any T-walk away from v0
--   the G-distance strictly increases except for backtracking steps, so a
--   T-cycle would force a strict decrease around the loop — impossible.
--
--   This is DEEP INPUT A of the decomposition of
--   CycleLengthsExp.ManyLengths.bfs_tree_prefix (parent, Open): it supplies the
--   BFS tree itself, while DEEP INPUT B (bfs_prefix_set) supplies the BFS prefix
--   set S. Together with the connectivity argument they assemble the parent node.
-- source:
--   Friedman–Krivelevich, Cycle lengths in expanding graphs, arXiv:1912.11011v2, p. 13, proof of Theorem 2, paragraph beginning 'Run the BFS algorithm'. DEEP INPUT A of the decomposition of CycleLengthsExp.ManyLengths.bfs_tree_prefix; see ~/workspace/p2m_harness/work/theorem_2/bfs_tree_prefix_decomp.lean (axiom bfs_parent_tree_ax, extracted verbatim).

import Mathlib
import Definitions.Def_CycleLengthsExp_ManyLengths_Setting

namespace CycleLengthsExp.ManyLengths

/-- Parent-choice tree / BFS tree (Friedman–Krivelevich, p. 13: "Run the BFS
algorithm ... until a tree T ... is obtained").

Given a set `S` containing `v₀` in which every vertex is `G`-reachable from
`v₀` and every non-root vertex has a parent in `S` one `G`-step closer to
`v₀`, there is a subgraph `T` on exactly the vertices `S` that is acyclic,
reaches every vertex of `S` from `v₀`, and preserves `G`-distances from `v₀`.

Proof sketch: choose the parent function by choice; `T`'s edges are the
parent edges (symmetrized). The parent chain from any `v ∈ S` back to `v₀`
is a `T`-walk of length `dist_G(v₀, v)`, so `dist_T ≤ dist_G`; every `T`-edge
is a `G`-edge, so `dist_G ≤ dist_T`. Acyclicity: along any `T`-walk away from
`v₀` the `G`-distance strictly increases except for backtracking steps, so
a `T`-cycle would force a strict decrease around the loop — impossible.
The delicate part is making the "no `T`-cycle" argument precise in Lean
(e.g. via a strictly-monotone potential on non-backtracking walks, or by
showing `T` is a forest by induction on the parent chains). -/
theorem bfs_parent_tree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (S : Set V) (v₀ : V) (hv₀ : v₀ ∈ S)
    (hreach : ∀ v ∈ S, G.Reachable v₀ v)
    (hparent : ∀ v ∈ S, v ≠ v₀ →
      ∃ u ∈ S, G.Adj u v ∧ G.dist v₀ u + 1 = G.dist v₀ v) :
    ∃ T : G.Subgraph, T.verts = S ∧ T.spanningCoe.IsAcyclic ∧
      (∀ v ∈ S, T.spanningCoe.Reachable v₀ v) ∧
      (∀ v ∈ S, T.spanningCoe.dist v₀ v = G.dist v₀ v) := by
  sorry

end CycleLengthsExp.ManyLengths
