-- Prove2me | Theorems.Thm_CycleLengthsExp_ManyLengths_branch_cycles_repaired
-- name    : CycleLengthsExp.ManyLengths.branch_cycles_repaired
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-18T08:17:28.627816+00:00
-- url     : https://prove2.me/theorems/44e9d28e-2561-4718-a82d-0aa984b75f10
-- title:
--   Branching + cycles, repaired (Friedman-Krivelevich p. 14): minimal subtree + branching -> |X3| >= |X1|/4 with distinct-length cycles C_w of length A + segLen w, assuming 2 <= |X1|
-- statement:
--   Branching + cycles (Friedman-Krivelevich, p. 14, proof of Theorem 2), REPAIRED VERSION.
--
--   The original node `CycleLengthsExp.ManyLengths.branch_cycles` (6f2911cf) is FALSE as stated: with X1 = {0} a singleton at a degree-1 vertex (counterexample: n=10, alpha=0.4, G = K9 on {1,...,9} plus pendant edge 0-1, S={2}, P = trivial walk at 0), all hypotheses hold but the conclusion forces X3 = {0} and demands a cycle at the degree-1 vertex 0, which does not exist (Walk.IsCycle excludes the nil walk, and every non-nil closed walk at 0 repeats the edge (0,1), so it is not a trail). See `work/theorem_2/branch_cycles_counterexample.md`.
--
--   This version adds the single hypothesis `2 <= X1.ncard`. With |X1| >= 2 the paper's pair-cycle argument goes through: attach each vertex of X1 to a level-j neighbour to form T2 (X1 vertices are leaves of T2); let T3 be the minimal subtree of T2 containing X1 with root r (the entry point from v0); dist_{T2}(r, w) is CONSTANT over w in X1. If r in X1, take X3 as the larger side of X1 \ {r} along P; if r not in X1, T3 - r has >= 2 branches meeting X1, discard a smallest branch Y and take X3 as the larger side of X1 \ Y along P w.r.t. a base vertex in Y. Either way |X3| >= |X1|/4, and the cycle C_w = P-segment ++ T2-path has length A + segLen w with A independent of w and segLen injective on X3, so the cycles have pairwise distinct lengths.
--
--   Given the BFS prefix tree T on S, the long path P in G minus S, and the extended tree T1 with the subset X1 of X0 attached to a single level j (the output of tree_extension_attach), plus 2 <= |X1|, there is a subset X3 of X1, a constant A, and a length function segLen such that |X3| >= |X1|/4, every w in X3 lies on a cycle C_w of length exactly A + segLen w, and segLen is injective on X3.
-- source:
--   Repair of 6f2911cf (false as stated). Triage: ~/workspace/p2m_harness/cyclelengths_branch_cycles_repair_triage_20261018.md. Counterexample: ~/workspace/p2m_harness/work/theorem_2/branch_cycles_counterexample.md.

import Mathlib
import Definitions.Def_CycleLengthsExp_ManyLengths_Setting

namespace CycleLengthsExp.ManyLengths

/-- REPAIRED 2026-10-18: the original `branch_cycles` (6f2911cf) is FALSE as stated
(pendant-vertex counterexample with X₁ = {0}; see `branch_cycles_counterexample.md`).
This version adds the hypothesis `hX₁card2 : 2 ≤ X₁.ncard`, which the paper's
pair-cycle argument needs (with |X₁| ≥ 2, both branching cases give |X₃| ≥ |X₁|/4
with genuine cycles; with |X₁| = 1 the conclusion can force a cycle at a degree-1
vertex, which does not exist). The assembly must discharge `2 ≤ X₁.ncard` by
raising n₀ (see triage report). Branching + cycles (Friedman–Krivelevich, p. 14: "Let T₂ be the tree
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
theorem branch_cycles_repaired (n : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
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
    (hX₁card2 : 2 ≤ X₁.ncard)
    (hattach : ∀ x ∈ X₁, ∃ y ∈ T₁.verts,
      CycleLengthsExp.WellSpread.level T₁ v₀ y = j ∧ G.Adj x y) :
    ∃ (X₃ : Set (Fin n)) (A : ℕ) (segLen : Fin n → ℕ),
      X₃ ⊆ X₁ ∧
      (X₁.ncard : ℝ) / 4 ≤ (X₃.ncard : ℝ) ∧
      (∀ w ∈ X₃, ∃ cyc : G.Walk w w, cyc.IsCycle ∧ cyc.length = A + segLen w) ∧
      Set.InjOn segLen X₃ := by
  sorry

end CycleLengthsExp.ManyLengths
