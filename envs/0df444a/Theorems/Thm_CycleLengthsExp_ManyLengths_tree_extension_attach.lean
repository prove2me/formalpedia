-- Prove2me | Theorems.Thm_CycleLengthsExp_ManyLengths_tree_extension_attach
-- name    : CycleLengthsExp.ManyLengths.tree_extension_attach
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-16T12:35:45.826535+00:00
-- url     : https://prove2.me/theorems/eaeaa519-1887-439b-8ed0-12c5ccc123f4
-- title:
--   Tree extension + attachment pigeonhole (Friedman-Krivelevich p. 14): |X1| >= |X0|/(k+1) attached to one level j of the extended tree T1
-- statement:
--   Tree extension + attachment pigeonhole (Friedman–Krivelevich, p. 14, proof of
--   Theorem 2: "Extend T by adding up to k-1 new levels using the BFS algorithm
--   while avoiding adding vertices of P ... At least |X0|/(k+1) vertices in X0
--   are adjacent to the same level in T1").
--
--   Given the BFS prefix tree T on the vertex set S (with root v0, max level m,
--   and the frontier property that neighbours outside S only touch the last two
--   levels of T) and the long path P in G minus S (disjoint from S), there is a
--   tree extension T1 of T — old vertices keep their levels, new vertices attach
--   outward, no vertex of P is ever added — with max level M1, together with a
--   subset X1 of X0 and a level j such that |X1| >= |X0|/(k+1) (where k = kNum
--   alpha) and every x in X1 has a neighbour y in T1 at level exactly j.
--
--   Why: every x in X0 has a connecting path Q_x of length at most k whose
--   internal vertices avoid S union P; Q_x starts in the last two levels of T by
--   the frontier property, and BFS from T avoiding P absorbs its vertices level
--   by level, so every x in X0 has a neighbour in the last k+1 levels of T1.
--   Pigeonhole over those k+1 levels gives X1 attached to a single level j.
--
--   This is the middle node of the three-node decomposition of theorem_2: it
--   consumes the BFS prefix tree (bfs_tree_prefix) and the long path P
--   (path_after_deletion), and its output (T1, X1, j) is exactly what
--   branch_cycles consumes to build the distinct-length cycles.
-- source:
--   Friedman–Krivelevich, proof of Theorem 2, p. 14 (extend T by BFS avoiding P; pigeonhole over k+1 levels gives |X1| >= |X0|/(k+1) attached to one level). Decomposition child of CycleLengthsExp.ManyLengths.theorem_2; see ~/workspace/p2m_harness/work/theorem_2/assembly_spec.lean (NEW NODE 2).

import Mathlib
import Definitions.Def_CycleLengthsExp_ManyLengths_Setting

namespace CycleLengthsExp.ManyLengths

/-- Tree extension + attachment pigeonhole (Friedman–Krivelevich, p. 14:
"Extend T by adding up to k-1 new levels using the BFS algorithm while
avoiding adding vertices of P ... At least |X₀|/(k+1) vertices in X₀ are
adjacent to the same level in T₁").

`T₁` is a TREE extension of `T` (old vertices keep their levels: new vertices
attach outward, so no shortcuts to old vertices are created). Every `x ∈ X₀`
has a neighbour in the last `k+1` levels of `T₁` because the connecting path
`Q_x` (length `≤ k`, internal vertices outside `S ∪ P`) starts in the last two
levels of `T` by `hTfront`, and BFS from `T` avoiding `P` absorbs its vertices
level by level. Pigeonhole over the `k+1` levels gives `X₁` attached to one
level `j`. This node is the middle of the three-node decomposition of
`CycleLengthsExp.ManyLengths.theorem_2` (parent, Open): it consumes the BFS
prefix tree of `bfs_tree_prefix` plus the long path `P` of
`path_after_deletion`, and feeds `branch_cycles`. -/
theorem tree_extension_attach (n : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (G : SimpleGraph (Fin n))
    (hG : CycleLengthsExp.WellSpread.IsAlphaExpander α G)
    (S : Set (Fin n)) (T : G.Subgraph) (v₀ : Fin n) (m : ℕ)
    (hScard : S.ncard = Nat.floor (α * (n : ℝ) / 4))
    (hTverts : T.verts = S)
    (hv₀ : v₀ ∈ S)
    (hTacyc : T.spanningCoe.IsAcyclic)
    (hTreach : ∀ v ∈ S, T.spanningCoe.Reachable v₀ v)
    (hTlev : ∀ v ∈ S, CycleLengthsExp.WellSpread.level T v₀ v ≤ m)
    (hTmax : ∃ v ∈ S, CycleLengthsExp.WellSpread.level T v₀ v = m)
    (hTfront : ∀ t ∈ S, ∀ q : Fin n, q ∉ S → G.Adj t q →
      m - 1 ≤ CycleLengthsExp.WellSpread.level T v₀ t)
    (u v : Fin n) (P : G.Walk u v) (hPpath : P.IsPath)
    (hPlen : P.length = Nat.ceil (α * (n : ℝ) / 4) - 1)
    (hPdisj : ∀ w ∈ P.support, w ∉ S) :
    ∃ (T₁ : G.Subgraph) (M₁ : ℕ) (X₁ : Set (Fin n)) (j : ℕ),
      (T.verts ⊆ T₁.verts ∧
        (∀ a b : Fin n, T.spanningCoe.Adj a b → T₁.spanningCoe.Adj a b)) ∧
      T₁.spanningCoe.IsAcyclic ∧
      (∀ w ∈ T₁.verts, T₁.spanningCoe.Reachable v₀ w) ∧
      (∀ w ∈ T₁.verts, CycleLengthsExp.WellSpread.level T₁ v₀ w ≤ M₁) ∧
      (∃ w ∈ T₁.verts, CycleLengthsExp.WellSpread.level T₁ v₀ w = M₁) ∧
      (∀ w ∈ T₁.verts, w ∉ P.support) ∧
      X₁ ⊆ CycleLengthsExp.ManyLengths.X0 α G S P ∧
      ((CycleLengthsExp.ManyLengths.X0 α G S P).ncard : ℝ) /
          ((CycleLengthsExp.ManyLengths.kNum α : ℝ) + 1) ≤ (X₁.ncard : ℝ) ∧
      (∀ x ∈ X₁, ∃ y ∈ T₁.verts,
        CycleLengthsExp.WellSpread.level T₁ v₀ y = j ∧ G.Adj x y) := by
  sorry

end CycleLengthsExp.ManyLengths
