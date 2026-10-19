-- Prove2me | Theorems.Thm_CycleLengthsExp_ManyLengths_bfs_prefix_set
-- name    : CycleLengthsExp.ManyLengths.bfs_prefix_set
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-17T20:00:17.051551+00:00
-- url     : https://prove2.me/theorems/6f253691-5138-499f-ab64-73bd30a398c4
-- title:
--   BFS prefix set (Friedman-Krivelevich p. 13): ball(r-1) subset S subset ball(r), |S| = N, attains radius r, parent one step closer to v0
-- statement:
--   BFS prefix set (Friedman–Krivelevich, p. 13, proof of Theorem 2: S is a PREFIX
--   of a full BFS tree — all of levels 1..m-1 plus some of level m).
--
--   Let G be a connected simple graph on Fin n (every vertex reachable from v0),
--   and let 1 <= N <= n. Then there exist a set S of vertices and a radius r
--   such that: S has exactly N vertices; v0 is in S; S contains the whole ball
--   of radius r-1 around v0 (every vertex with dist_G(v0, v) <= r-1 is in S);
--   S is contained in the ball of radius r (every vertex of S has
--   dist_G(v0, v) <= r); some vertex of S attains radius r (dist_G(v0, v) = r);
--   and every non-root vertex v of S has a parent u in S with u adjacent to v
--   in G and dist_G(v0, u) + 1 = dist_G(v0, v) (one G-step closer to v0).
--
--   Why: let B_k be the ball of radius k around v0. B_0 = {v0} has size 1, and
--   the balls increase to the whole vertex set by connectedness, so let r be the
--   least k with |B_k| >= N; then |B_{r-1}| < N <= |B_r| (with B_{-1} empty),
--   and take S = B_{r-1} together with any N - |B_{r-1}| vertices of the sphere
--   {dist = r}. The parent property follows from the predecessor lemma: any
--   reachable v != v0 has a neighbour u with dist(v0, u) + 1 = dist(v0, v)
--   (take a shortest walk, its penultimate vertex). The predecessor lemma is
--   elementary and should be proved for real inside B's proof, not axiomatized.
--
--   This is DEEP INPUT B of the decomposition of
--   CycleLengthsExp.ManyLengths.bfs_tree_prefix (parent, Open): it supplies the
--   BFS prefix set S, while DEEP INPUT A (bfs_parent_tree, published) supplies
--   the BFS tree itself. Together with the connectivity argument they assemble
--   the parent node.
-- source:
--   Friedman–Krivelevich, Cycle lengths in expanding graphs, arXiv:1912.11011v2, p. 13, proof of Theorem 2 (BFS prefix). DEEP INPUT B of the decomposition of CycleLengthsExp.ManyLengths.bfs_tree_prefix; see ~/workspace/p2m_harness/work/theorem_2/bfs_tree_prefix_decomp.lean (axiom bfs_prefix_set_ax, extracted verbatim).

import Mathlib
import Definitions.Def_CycleLengthsExp_ManyLengths_Setting

namespace CycleLengthsExp.ManyLengths

/-- BFS prefix set (Friedman–Krivelevich, p. 13: `S` is a PREFIX of a full
BFS tree — all of levels `1..m-1` plus some of level `m`).

Stated in `G`-distance terms (level = `dist + 1`, so `r = m - 1`): given a
connected graph `G` on `Fin n`, a root `v₀`, and `1 ≤ N ≤ n`, there are a set
`S` and a radius `r` such that `S` has exactly `N` vertices, contains `v₀`,
contains the whole ball of radius `r - 1`, is contained in the ball of
radius `r`, attains radius `r`, and every non-root vertex of `S` has a
parent in `S` one step closer to `v₀` (the predecessor on a shortest
`v₀`–`v` path, which lies in the ball of radius `r - 1 ⊆ S`).

Proof sketch: let `B_k = {v | dist_G(v₀, v) ≤ k}`. `B_0 = {v₀}` has size 1,
`B_k ↑ univ` (connectedness: every vertex is reachable), so let `r` be the
least `k` with `|B_k| ≥ N`; then `|B_{r-1}| < N ≤ |B_r|` (with `B_{-1} = ∅`),
and take `S = B_{r-1} ∪ (any N - |B_{r-1}| vertices of the sphere
{dist = r})`. The parent property follows from the predecessor lemma:
any reachable `v ≠ v₀` has a neighbour `u` with `dist(v₀, u) + 1 = dist(v₀, v)`
(take a shortest walk, its penultimate vertex). The predecessor lemma itself
is elementary (`Reachable.exists_walk_length_eq_dist` + `Walk.concat` /
`dropLast`) and should be proved for real inside `B`'s proof, not axiomatized. -/
theorem bfs_prefix_set (n : ℕ) (G : SimpleGraph (Fin n)) (v₀ : Fin n) (N : ℕ)
    (hconn : ∀ v, G.Reachable v₀ v) (hN1 : 1 ≤ N) (hNn : N ≤ n) :
    ∃ (S : Set (Fin n)) (r : ℕ),
      S.ncard = N ∧ v₀ ∈ S ∧
      (∀ v, G.dist v₀ v ≤ r - 1 → v ∈ S) ∧
      (∀ v ∈ S, G.dist v₀ v ≤ r) ∧
      (∃ v ∈ S, G.dist v₀ v = r) ∧
      (∀ v ∈ S, v ≠ v₀ →
        ∃ u ∈ S, G.Adj u v ∧ G.dist v₀ u + 1 = G.dist v₀ v) := by
  sorry

end CycleLengthsExp.ManyLengths
