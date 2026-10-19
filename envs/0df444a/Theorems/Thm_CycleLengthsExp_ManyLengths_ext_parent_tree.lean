-- Prove2me | Theorems.Thm_CycleLengthsExp_ManyLengths_ext_parent_tree
-- name    : CycleLengthsExp.ManyLengths.ext_parent_tree
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-17T20:09:45.402153+00:00
-- url     : https://prove2.me/theorems/0b696241-0045-479d-bdfa-c5aaaec555e0
-- title:
--   Extension parent tree (Friedman-Krivelevich p. 14): BFS extension of T to W with exact level formula dist_T1(v0,w) = dist_T(v0, r w) + h w
-- statement:
--   Extension parent tree (Friedman–Krivelevich, p. 14, proof of Theorem 2:
--   "Extend T by adding up to k-1 new levels using the BFS algorithm while
--   avoiding adding vertices of P").
--
--   Let G be a finite simple graph with decidable equality on vertices, S a set
--   of vertices, and T a subgraph of G with vertex set exactly S, rooted at
--   v0 in S, acyclic, reaching every vertex of S from v0. Let W be a superset
--   of S with a height function h : V -> N that is 0 on S and positive off S,
--   such that every w in W \ S has a neighbour u in W with h u + 1 = h w
--   (the parent property).
--
--   Then there is a subgraph T1 of G with vertex set exactly W, extending T
--   (every T-edge is a T1-edge), acyclic, reaching every vertex of W from v0,
--   together with a root function r : V -> V such that: r w lies in S for
--   w in W; r w = w for w in S; the exact level formula holds,
--   dist_{T1}(v0, w) = dist_T(v0, r w) + h w for all w in W; and every
--   w in W \ S has its root r w adjacent in G to some vertex outside S
--   (the h = 1 vertex on w's parent chain).
--
--   Why: choose the parent function by choice from the parent property; T1's
--   edges are T's edges plus the symmetrized parent edges. Acyclicity is a
--   max-h argument on closed T1-paths; the distance formula has an upper bound
--   via the T-path to r w plus the parent chain and a lower bound via the
--   root-projection argument (parent edges change h by exactly +/-1).
--
--   This is DEEP INPUT A2 of the decomposition of
--   CycleLengthsExp.ManyLengths.tree_extension_attach (parent, Open): it supplies
--   the BFS extension tree itself, while DEEP INPUT B2 (dist_avoid_pred, proved
--   for real) supplies the distance-to-S-avoiding-P height function. Together
--   with the attachment-pigeonhole argument they assemble the parent node.
-- source:
--   Friedman–Krivelevich, Cycle lengths in expanding graphs, arXiv:1912.11011v2, p. 14, proof of Theorem 2, paragraph beginning 'Extend T by adding up to k-1 new levels using the BFS algorithm'. DEEP INPUT A2 of the decomposition of CycleLengthsExp.ManyLengths.tree_extension_attach; see ~/workspace/p2m_harness/work/theorem_2/tree_extension_attach_decomp.lean (axiom ext_parent_tree_ax, extracted verbatim).

import Mathlib

namespace CycleLengthsExp.ManyLengths

/-- Extension parent tree (Friedman–Krivelevich, p. 14: "Extend T by adding
up to k-1 new levels using the BFS algorithm while avoiding adding vertices
of P").

Given a tree `T` on `S` (rooted at `v₀`, acyclic, reaching every vertex of
`S`) and a superset `W ⊇ S` with a height function `h` (0 on `S`, positive
off `S`) and the parent property (every `w ∈ W ∖ S` has a neighbour in `W`
with `h` one less), there is a subgraph `T₁` on exactly the vertices `W`
extending `T`, acyclic, reaching every vertex of `W` from `v₀`, with the
EXACT level formula `dist_{T₁}(v₀, w) = dist_T(v₀, r w) + h w` for a root
function `r : V → V` (the parent-chain endpoint in `S`, identity on `S`),
and every `w ∈ W ∖ S` has its root `r w` adjacent to some vertex outside
`S` (the `h = 1` vertex on `w`'s parent chain — this is what feeds the
frontier hypothesis in the assembly).

Proof sketch: choose a parent function `p` by choice from `hparent` (for
`w ∈ W ∖ S` pick `u` with `h u + 1 = h w`; `p` is only used on `W ∖ S`).
Let `T₁.verts = W` and `T₁.Adj` be `T.Adj` plus the symmetrized parent
edges. Acyclicity: max-`h` argument on closed `T₁`-paths — a vertex of
maximal `h` on a nontrivial closed path has two distinct `T₁`-neighbours,
both of `h` one less, but it has only one parent edge and `T`-edges
require `h = 0` (the all-`h = 0` case reduces to `T`-acyclicity).
Dist formula: upper bound via the `T`-path to `r w` plus the parent chain;
lower bound via the root-projection argument (every `T₁`-edge either
preserves `r` or is a `T`-edge; parent edges change `h` by exactly ±1,
so any `T₁`-path from `v₀` to `w` has length at least
`dist_T (v₀, r w) + h w`). Frontier-neighbour: the `h = 1` vertex on `w`'s
parent chain is outside `S` and adjacent to `r w`. -/
theorem ext_parent_tree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (S : Set V) (T : G.Subgraph) (v₀ : V)
    (hTverts : T.verts = S) (hv₀ : v₀ ∈ S)
    (hTacyc : T.spanningCoe.IsAcyclic)
    (hTreach : ∀ v ∈ S, T.spanningCoe.Reachable v₀ v)
    (W : Set V) (hSW : S ⊆ W)
    (h : V → ℕ) (hhS : ∀ w ∈ S, h w = 0) (hhW : ∀ w ∈ W, w ∉ S → 0 < h w)
    (hparent : ∀ w ∈ W, w ∉ S → ∃ u ∈ W, G.Adj u w ∧ h u + 1 = h w) :
    ∃ (T₁ : G.Subgraph) (r : V → V),
      T₁.verts = W ∧
      (∀ a b, T.spanningCoe.Adj a b → T₁.spanningCoe.Adj a b) ∧
      T₁.spanningCoe.IsAcyclic ∧
      (∀ w ∈ W, T₁.spanningCoe.Reachable v₀ w) ∧
      (∀ w ∈ W, r w ∈ S) ∧
      (∀ w ∈ S, r w = w) ∧
      (∀ w ∈ W, T₁.spanningCoe.dist v₀ w = T.spanningCoe.dist v₀ (r w) + h w) ∧
      (∀ w ∈ W, w ∉ S → ∃ z, z ∉ S ∧ G.Adj (r w) z) := by
  sorry

end CycleLengthsExp.ManyLengths
