-- Prove2me | Theorems.Thm_CycleLengthsExp_ManyLengths_bcr_branching
-- name    : CycleLengthsExp.ManyLengths.bcr_branching
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-18T16:01:42.930224+00:00
-- url     : https://prove2.me/theorems/1822dab5-b59a-4424-9d5d-c70962ba34a7
-- title:
--   Branching + T-leg (Friedman-Krivelevich p. 14): smallest branch Y, base w0, T-leg paths of length 2d+2 for w outside Y
-- statement:
--   Branching + T-leg (Friedman-Krivelevich, p. 14, proof of Theorem 2).
--
--   Setup: T1 is an acyclic subtree of G rooted at v0, X1 is a set of vertices
--   outside T1 with at least 2 elements, and every x in X1 has a chosen
--   attachment y(x) in T1 at level exactly j adjacent to x in G. (Think of X1
--   as leaves attached to level j of T1; the attachments come from
--   tree_extension_attach.)
--
--   Conclusion: there exist a common distance d, a smallest branch Y subset X1
--   with |Y| <= |X1| / 2, and a base vertex w0 in Y, such that for every
--   w in X1 \ Y there is a path q in G from w to w0 of length exactly
--   2*d + 2 whose support lies in {w, w0} together with the vertices of T1.
--
--   Why: let C be the set of vertices z of T1 lying on every v0 -> y(x) path in
--   T1 (v0 is in C). Take r in C maximizing dist_T1(v0, r) (a finite nonempty
--   maximum). Then dist_T1(r, y(x)) = (j - 1) - dist_T1(v0, r) =: d is the SAME
--   for all x, by level additivity. Partition X1 by branch: branch(x) is the
--   first step from r on the path r -> y(x), or x itself if y(x) = r. There are
--   at least 2 classes (otherwise a deeper vertex would lie on every path,
--   contradicting maximality of r, or all y(x) = r and the branches are the
--   distinct x's). Let Y be a smallest class, w0 in Y. For w in X1 \ Y, the
--   T1-path y(w) -> y(w0) has length 2*d: the concatenation (reverse of
--   r -> y(w)) ++ (r -> y(w0)) is a path because the two subpaths from r start
--   with different first steps (different branches), hence meet only at r
--   (tree path uniqueness). Transfer the T1-walk to a G-walk by step induction,
--   then prepend/append the two attachment edges to get the T-leg q of length
--   1 + 2*d + 1, with support in {w, w0} plus T1 vertices.
--
--   This is DEEP INPUT A of the decomposition of
--   CycleLengthsExp.ManyLengths.branch_cycles_repaired (parent, Open): the
--   assembly consumes d, Y, w0 and the T-legs to build one cycle per w in X3,
--   with X3 the larger side of X1 \ Y along P.
-- source:
--   Friedman–Krivelevich, Cycle lengths in expanding graphs, arXiv:1912.11011v2, p. 14, proof of Theorem 2 (minimal subtree + branching). DEEP INPUT A of the decomposition of CycleLengthsExp.ManyLengths.branch_cycles_repaired; see ~/workspace/p2m_harness/work/theorem_2/branch_cycles_repaired_decomp.lean (axiom bcr_branching, extracted verbatim).

import Mathlib
import Definitions.Def_CycleLengthsExp_ManyLengths_Setting

namespace CycleLengthsExp.ManyLengths

/-- Branching + T-leg (Friedman–Krivelevich, p. 14, proof of Theorem 2).

Setup: `T₁` is an acyclic subtree of `G` rooted at `v₀`, `X₁` is a set of
vertices outside `T₁` (at least 2 of them), and every `x ∈ X₁` has a chosen
attachment `y x ∈ T₁.verts` at level exactly `j` adjacent to `x` in `G`.
(Think of `X₁` as leaves attached to level `j` of `T₁`; the attachments
come from `tree_extension_attach`.)

Conclusion: there are a common distance `d`, a smallest branch `Y ⊆ X₁`
with `|Y| ≤ |X₁| / 2`, and a base vertex `w₀ ∈ Y`, such that for every
`w ∈ X₁ ∖ Y` there is a path `q` in `G` from `w` to `w₀` of length exactly
`2 * d + 2` whose support lies in `{w, w₀} ∪ T₁.verts`.

Proof sketch: choose the attachments `y` via choice. Let `C` be the set of
vertices `z ∈ T₁.verts` lying on every `v₀ → y_x` path in `T₁` (`v₀ ∈ C`).
Take `r ∈ C` maximizing `dist_{T₁}(v₀, r)` (finite nonempty max). Then
`dist_{T₁}(r, y_x) = (j - 1) - dist_{T₁}(v₀, r) =: d` is the SAME for all `x`,
by level additivity. Partition `X₁` by branch: `branch(x)` is the first
step from `r` on the path `r → y_x`, or `x` itself if `y_x = r`. There are
at least 2 classes (else a deeper vertex would lie on every path,
contradicting maximality of `r`, or all `y_x = r` and the branches are the
distinct `x`'s). Let `Y` be a smallest class, `w₀ ∈ Y`. For `w ∈ X₁ ∖ Y`,
the `T₁`-path `y_w → y_{w₀}` has length `2 * d`: the concatenation
(reverse of `r → y_w`) ++ (`r → y_{w₀}`) is a path because the two subpaths
from `r` start with different first steps (different branches), hence meet
only at `r` (tree path uniqueness). Transfer the `T₁`-walk to a `G`-walk by
step induction, then prepend/append the two attachment edges to get the
`T`-leg `q` of length `1 + 2 * d + 1`, with support in `{w, w₀} ∪ T₁.verts`.

This is DEEP INPUT A of the decomposition of
`CycleLengthsExp.ManyLengths.branch_cycles_repaired` (parent, Open): the
assembly consumes `d`, `Y`, `w₀` and the `T`-legs to build one cycle per
`w ∈ X₃`, with `X₃` the larger side of `X₁ ∖ Y` along `P`. -/
theorem bcr_branching (n : ℕ) (G : SimpleGraph (Fin n))
    (T₁ : G.Subgraph) (v₀ : Fin n) (X₁ : Set (Fin n)) (j : ℕ)
    (y : ∀ (x : Fin n), x ∈ X₁ → Fin n)
    (hT₁acyc : T₁.spanningCoe.IsAcyclic)
    (hT₁reach : ∀ w ∈ T₁.verts, T₁.spanningCoe.Reachable v₀ w)
    (hv₀ : v₀ ∈ T₁.verts)
    (hX₁T₁ : ∀ x ∈ X₁, x ∉ T₁.verts)
    (hy : ∀ (x : Fin n) (hx : x ∈ X₁), y x hx ∈ T₁.verts ∧
      CycleLengthsExp.WellSpread.level T₁ v₀ (y x hx) = j ∧ G.Adj x (y x hx))
    (hX₁card2 : 2 ≤ X₁.ncard) :
    ∃ (d : ℕ) (Y : Set (Fin n)) (w₀ : Fin n),
      Y ⊆ X₁ ∧ w₀ ∈ Y ∧ (Y.ncard : ℝ) ≤ (X₁.ncard : ℝ) / 2 ∧
      (∀ w : Fin n, w ∈ X₁ ∧ w ∉ Y → ∃ q : G.Walk w w₀, q.IsPath ∧ q.length = 2 * d + 2 ∧
        (∀ z ∈ q.support, z = w ∨ z = w₀ ∨ z ∈ T₁.verts)) := by
  sorry

end CycleLengthsExp.ManyLengths
