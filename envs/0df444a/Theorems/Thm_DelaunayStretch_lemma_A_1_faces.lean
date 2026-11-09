-- Prove2me | Theorems.Thm_DelaunayStretch_lemma_A_1_faces
-- name    : DelaunayStretch.lemma_A_1_faces
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:52:33.448762+00:00
-- url     : https://prove2.me/theorems/d2023286-fce0-4d6f-9f8b-58dc79792eba
-- title:
--   Lemma A.1 — faces of the Delaunay subdivision: vertices, covering, edges, intersections
-- statement:
--   Let $S\subset\mathbb R^2$ be finite and $D$ a Delaunay triangulation of $S$; for $T\in D$ let $O_T$ be its closed circumdisk and $F_T=\mathrm{conv}(S\cap\partial O_T)$.
--
--   1. For every $T\in D$, the face $F_T$ is a convex polygon whose vertex set is $S\cap\partial O_T$. The triangles of $D$ contained in $F_T$ are exactly the triangles $T'\in D$ with $\partial O_{T'}=\partial O_T$, and they cover $F_T$. In particular, the faces cover the convex hull of $S$.
--   2. Every edge of a face is an edge of $D$.
--   3. Any two distinct faces are disjoint, or meet in a common vertex, or meet in a common edge.
--
--   The faces replace triangles with a common circumcircle, so that the circumdisks met by a segment form a disk chain.
--
--   **Formalization Note** Vertices of a face are its extreme points; a triangle contained in $F_T$ means its convex hull is; an edge of a face is a segment between two distinct vertices lying on the boundary of the face; an edge of $D$ is a side of a triangle of $D$.
--
--   Differences from the source:
--   - encoding: F_T is a convex polygon whose vertex set is S ∩ ∂O_T → the extreme points of F_T = conv(S ∩ ∂O_T) are S ∩ ∂O_T; reason: F_T is a convex polygon by definition (the convex hull of a finite set) and its vertices are its extreme points
--   - encoding: edge of a face → segment between two distinct extreme points contained in the boundary of the face; reason: for a convex polygon with nonempty interior these are exactly its sides
--   - encoding: points of ℝ² with coordinates x(z), y(z) and Euclidean norm → points of ℂ with x = re, y = im and ‖z − w‖ = dist z w; reason: ℂ is ℝ² with the Euclidean norm; same instances
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), Lemma A.1, p.48

import Mathlib
import Definitions.Def_DelaunayStretch_face

namespace DelaunayStretch

/-- **Lemma A.1 (Faces)** (p.48). Let `S ⊂ ℝ²` be finite and `D` a Delaunay triangulation of
`S`; for `T ∈ D` let `O_T` be its closed circumdisk and `F_T = conv(S ∩ ∂O_T)` its face.

1. For every `T ∈ D`, the face `F_T` is a convex polygon whose vertex set is `S ∩ ∂O_T`. The
   triangles of `D` contained in `F_T` are exactly the triangles `T′ ∈ D` with `∂O_T′ = ∂O_T`,
   and they cover `F_T`. In particular, the faces cover the convex hull of `S`.
2. Every edge of a face is an edge of `D`.
3. Any two distinct faces are disjoint, or meet in a common vertex, or meet in a common edge.

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026), Lemma A.1, p.48 (standing assumptions and definition of faces, p.48).

**Formalization Note** The vertex set of the polygon `F_T` is its set of extreme points; `F_T`
is convex by definition (a convex hull). A triangle `T′` "contained in `F_T`" means
`conv T′ ⊆ F_T`. An edge of a face is a segment between two distinct vertices that lies on its
boundary (`IsFaceEdge`); an edge of `D` is a side of a triangle of `D` (`IsEdgeOf`). -/
theorem lemma_A_1_faces (S : Finset ℂ) (D : Finset (Finset ℂ)) (hD : IsDelaunayTriangulation S D) :
    (∀ T ∈ D,
      Set.extremePoints ℝ (face S T) = (S : Set ℂ) ∩ circumcircle T ∧
      (∀ T' ∈ D, convexHull ℝ (T' : Set ℂ) ⊆ face S T ↔ circumcircle T' = circumcircle T) ∧
      (⋃ T' ∈ D, ⋃ (_ : circumcircle T' = circumcircle T), convexHull ℝ (T' : Set ℂ)) =
        face S T) ∧
    (⋃ T ∈ D, face S T) = convexHull ℝ (S : Set ℂ) ∧
    (∀ F : Set ℂ, IsFace S D F → ∀ x y : ℂ, IsFaceEdge F x y → IsEdgeOf D x y) ∧
    (∀ F F' : Set ℂ, IsFace S D F → IsFace S D F' → F ≠ F' →
      F ∩ F' = ∅ ∨
      (∃ p : ℂ, p ∈ Set.extremePoints ℝ F ∧ p ∈ Set.extremePoints ℝ F' ∧ F ∩ F' = {p}) ∨
      (∃ x y : ℂ, IsFaceEdge F x y ∧ IsFaceEdge F' x y ∧ F ∩ F' = segment ℝ x y)) := by sorry

end DelaunayStretch
