-- Prove2me | Theorems.Thm_CycleLengthsExp_ManyLengths_branch_cycles
-- name    : CycleLengthsExp.ManyLengths.branch_cycles
-- status  : Open
-- author  : @junyihjy
-- created : 2026-10-16T16:01:09.374796+00:00
-- url     : https://prove2.me/theorems/6f2911cf-a9e7-470a-86e4-4716ae8576c4
-- title:
--   Branching + cycles (Friedman-Krivelevich p. 14): minimal subtree + branching -> |X3| >= |X1|/4 with distinct-length cycles C_w of length A + segLen w
-- statement:
--   Branching + cycles (Friedman–Krivelevich, p. 14, proof of Theorem 2: "Let T2
--   be the tree obtained by connecting each vertex in X1 to one of its neighbors
--   in the last level of T1. Let T3 be the minimal subtree of T2 containing X1
--   and let v be its root ... One of the branches contains at most half of the
--   vertices of X1, denote this set by Y and let X2 = X1 minus Y ... at least
--   half of the vertices of X2 appear on P on the same side of u ... Finally we
--   construct a cycle C_w for every w in X3 ... As the lengths of the cycles
--   {C_w} are all distinct ...").
--
--   Given the BFS prefix tree T on S, the long path P in G minus S, and the
--   extended tree T1 with the subset X1 of X0 attached to a single level j (the
--   output of tree_extension_attach), there is a subset X3 of X1, a constant A,
--   and a length function segLen such that |X3| >= |X1|/4, every w in X3 lies on
--   a cycle C_w of length exactly A + segLen w, and segLen is injective on X3 —
--   so the cycles C_w have pairwise distinct lengths.
--
--   Why: attach each vertex of X1 to one of its neighbours in the last level of
--   T1 to form T2; let T3 be the minimal subtree of T2 containing X1 with root v.
--   One branch of T3 holds at most half of X1; discarding it (X2 = X1 minus that
--   branch) and then keeping the half of X2 lying on the same side of u along P
--   gives X3 with |X3| >= |X1|/4. Every w in X1 is a leaf of T2 attached to a
--   level-j vertex, so dist_{T3}(w, v) is constant over w in X1; hence C_w has
--   length dist(v,u) + dist_P(u,w) + dist_{T3}(w,v) = A + dist_P(u,w) with A
--   independent of w, and w |-> dist_P(u,w) is injective on X3 because all of X3
--   lies on the same side of u along P.
--
--   This is the last node of the three-node decomposition of theorem_2: its
--   output (X3, A, segLen) is exactly what the assembly counts to get
--   Omega(alpha^3/log(1/alpha)) n distinct cycle lengths.
-- source:
--   Friedman–Krivelevich, proof of Theorem 2, p. 14 (minimal subtree T3 + branching gives |X3| >= |X1|/4; cycles C_w of length A + segLen w with segLen injective). Decomposition child of CycleLengthsExp.ManyLengths.theorem_2; see ~/workspace/p2m_harness/work/theorem_2/assembly_spec.lean (NEW NODE 3).

import Mathlib
import Definitions.Def_CycleLengthsExp_ManyLengths_Setting

namespace CycleLengthsExp.ManyLengths

/-- Branching + cycles (Friedman–Krivelevich, p. 14: "Let T₂ be the tree
obtained by connecting each vertex in X₁ to one of its neighbors in the last
level of T₁. Let T₃ be the minimal subtree of T₂ containing X₁ and let v be
its root ... One of the branches contains at most half of the vertices of X₁,
denote this set by Y and let X₂ = X₁ ∖ Y ... at least half of the vertices of
X₂ appear on P on the same side of u ... Finally we construct a cycle C_w for
every w ∈ X₃ ... As the lengths of the cycles {C_w} are all distinct ...").

Why the lengths are distinct: every `w ∈ X₁` is a leaf of `T₂` attached to a
level-`j` vertex, so `dist_{T₃}(w, v) = j - depth(v)` is CONSTANT over
`w ∈ X₁`; `C_w` has length `dist(v,u) + dist_P(u,w) + dist_{T₃}(w,v) =
A + dist_P(u,w)` with `A` independent of `w`, and `w ↦ dist_P(u,w)` is
injective on `X₃` because all of `X₃` lies on the same side of `u` along the
path `P`. The statement packages exactly what the assembly consumes: the
cycles, the constant `A`, an injective length function `segLen`, and the
`|X₃| ≥ |X₁|/4` count. The `T₂`/`T₃`/branching machinery is internal to this
node's proof. This node is the last of the three-node decomposition of
`CycleLengthsExp.ManyLengths.theorem_2` (parent, Open): it consumes the
extended tree `T₁`, the set `X₁` and the level `j` of `tree_extension_attach`,
and its output (X₃, A, segLen) is exactly what the assembly counts to get
`Ω(α³/log(1/α))n` distinct cycle lengths. -/
theorem branch_cycles (n : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
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
    (hPdisj : ∀ w ∈ P.support, w ∉ S)
    (T₁ : G.Subgraph) (M₁ : ℕ) (X₁ : Set (Fin n)) (j : ℕ)
    (hText : T.verts ⊆ T₁.verts ∧
      (∀ a b : Fin n, T.spanningCoe.Adj a b → T₁.spanningCoe.Adj a b))
    (hT₁acyc : T₁.spanningCoe.IsAcyclic)
    (hT₁reach : ∀ w ∈ T₁.verts, T₁.spanningCoe.Reachable v₀ w)
    (hT₁lev : ∀ w ∈ T₁.verts, CycleLengthsExp.WellSpread.level T₁ v₀ w ≤ M₁)
    (hT₁max : ∃ w ∈ T₁.verts, CycleLengthsExp.WellSpread.level T₁ v₀ w = M₁)
    (hT₁avoid : ∀ w ∈ T₁.verts, w ∉ P.support)
    (hX₁sub : X₁ ⊆ CycleLengthsExp.ManyLengths.X0 α G S P)
    (hX₁card : ((CycleLengthsExp.ManyLengths.X0 α G S P).ncard : ℝ) /
        ((CycleLengthsExp.ManyLengths.kNum α : ℝ) + 1) ≤ (X₁.ncard : ℝ))
    (hattach : ∀ x ∈ X₁, ∃ y ∈ T₁.verts,
      CycleLengthsExp.WellSpread.level T₁ v₀ y = j ∧ G.Adj x y) :
    ∃ (X₃ : Set (Fin n)) (A : ℕ) (segLen : Fin n → ℕ),
      X₃ ⊆ X₁ ∧
      (X₁.ncard : ℝ) / 4 ≤ (X₃.ncard : ℝ) ∧
      (∀ w ∈ X₃, ∃ cyc : G.Walk w w, cyc.IsCycle ∧ cyc.length = A + segLen w) ∧
      Set.InjOn segLen X₃ := by
  sorry

end CycleLengthsExp.ManyLengths
