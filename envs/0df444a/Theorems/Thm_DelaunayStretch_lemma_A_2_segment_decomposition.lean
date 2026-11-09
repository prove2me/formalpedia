-- Prove2me | Theorems.Thm_DelaunayStretch_lemma_A_2_segment_decomposition
-- name    : DelaunayStretch.lemma_A_2_segment_decomposition
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:52:45.860082+00:00
-- url     : https://prove2.me/theorems/68740d0a-4276-4b44-9106-b48c455df647
-- title:
--   Lemma A.2 — a segment $[u,v]$ crosses a sequence of faces through common edges
-- statement:
--   Let $S\subset\mathbb R^2$ be finite and $D$ a Delaunay triangulation of $S$. Let $u\ne v$ be points of $S$ such that the open segment $(u,v)$ contains no point of $S$, and suppose that $[u,v]$ is not an edge of $D$. Then there are pairwise distinct faces $F_1,\dots,F_m$, $m\ge1$, and pairwise distinct points $z_0=u,z_1,\dots,z_m=v$, in this order along $[u,v]$, such that:
--
--   1. $[u,v]\cap F_i=[z_{i-1},z_i]$ for $1\le i\le m$;
--   2. for $1\le i\le m-1$, the faces $F_i$ and $F_{i+1}$ have a common edge $E_i$, the point $z_i$ lies in the relative interior of $E_i$, and $E_i$ does not lie on the line through $u$ and $v$;
--   3. $u$ is a vertex of $F_1$, $v$ is a vertex of $F_m$, and $E_{i-1}\ne E_i$ for $2\le i\le m-1$.
--
--   The circumdisks of these faces form the disk chain of the reduction (Lemma A.3).
--
--   **Formalization Note** "In this order along $[u,v]$" is $z_i=u+t_i(v-u)$ with $0=t_0<t_1<\dots<t_m=1$; $E_i$ is the segment between two points $e_i$, $e'_i$; its relative interior is the open segment; "does not lie on the line" is "not both ends on the line"; vertices are extreme points.
--
--   Differences from the source:
--   - encoding: pairwise distinct points z₀ = u, …, z_m = v in this order along [u, v] → zᵢ = u + tᵢ (v − u) with 0 = t₀ < t₁ < ⋯ < t_m = 1; reason: points of [u, v] in this order are exactly such parameters
--   - encoding: points of ℝ² with coordinates x(z), y(z) and Euclidean norm → points of ℂ with x = re, y = im and ‖z − w‖ = dist z w; reason: ℂ is ℝ² with the Euclidean norm; same instances
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), Lemma A.2, pp.49–50

import Mathlib
import Definitions.Def_DelaunayStretch_face

namespace DelaunayStretch

/-- **Lemma A.2 (Segment decomposition)** (pp.49–50). Let `S ⊂ ℝ²` be finite and `D` a
Delaunay triangulation of `S`. Let `u ≠ v` be points of `S` such that the open segment `(u, v)`
contains no point of `S`, and suppose that `[u, v]` is not an edge of `D`. Then there are
pairwise distinct faces `F₁, …, Fₘ`, where `m ≥ 1`, and pairwise distinct points
`z₀ = u, z₁, …, zₘ = v`, in this order along `[u, v]`, such that

1. `[u, v] ∩ Fᵢ = [zᵢ₋₁, zᵢ]` for `1 ≤ i ≤ m`;
2. for `1 ≤ i ≤ m − 1`, the faces `Fᵢ` and `Fᵢ₊₁` have a common edge `Eᵢ`, the point `zᵢ` lies
   in the relative interior of `Eᵢ`, and `Eᵢ` does not lie on the line through `u` and `v`;
3. `u` is a vertex of `F₁`, `v` is a vertex of `Fₘ`, and `Eᵢ₋₁ ≠ Eᵢ` for `2 ≤ i ≤ m − 1`.

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026), Lemma A.2, pp.49–50.

**Formalization Note** "In this order along `[u, v]`": `zᵢ = u + tᵢ (v − u)`
(`AffineMap.lineMap u v tᵢ`) with `0 = t₀ < t₁ < ⋯ < tₘ = 1`. The common edge `Eᵢ` is the
segment `[eᵢ, e′ᵢ]`, an edge (`IsFaceEdge`) of both faces; its relative interior is the open
segment; "does not lie on the line through `u` and `v`" is "not both ends on that line".
Vertices of a face are its extreme points. -/
theorem lemma_A_2_segment_decomposition (S : Finset ℂ) (D : Finset (Finset ℂ))
    (hD : IsDelaunayTriangulation S D) (u v : ℂ) (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v)
    (hopen : ∀ p ∈ S, p ∉ openSegment ℝ u v) (hnot : ¬ IsEdgeOf D u v) :
    ∃ (m : ℕ) (F : ℕ → Set ℂ) (t : ℕ → ℝ) (e e' : ℕ → ℂ),
      1 ≤ m ∧
      (∀ i, 1 ≤ i → i ≤ m → IsFace S D (F i)) ∧
      (∀ i j, 1 ≤ i → i ≤ m → 1 ≤ j → j ≤ m → i ≠ j → F i ≠ F j) ∧
      t 0 = 0 ∧ t m = 1 ∧ (∀ i, i < m → t i < t (i + 1)) ∧
      (∀ i, 1 ≤ i → i ≤ m →
        segment ℝ u v ∩ F i =
          segment ℝ (AffineMap.lineMap u v (t (i - 1))) (AffineMap.lineMap u v (t i))) ∧
      (∀ i, 1 ≤ i → i + 1 ≤ m →
        IsFaceEdge (F i) (e i) (e' i) ∧ IsFaceEdge (F (i + 1)) (e i) (e' i) ∧
          AffineMap.lineMap u v (t i) ∈ openSegment ℝ (e i) (e' i) ∧
          ¬ (e i ∈ line[ℝ, u, v] ∧ e' i ∈ line[ℝ, u, v])) ∧
      u ∈ Set.extremePoints ℝ (F 1) ∧ v ∈ Set.extremePoints ℝ (F m) ∧
      (∀ i, 2 ≤ i → i + 1 ≤ m →
        segment ℝ (e (i - 1)) (e' (i - 1)) ≠ segment ℝ (e i) (e' i)) := by sorry

end DelaunayStretch
