-- Prove2me | Theorems.Thm_CorrColoring_ThreeChoosable_plane_precoloring_extension
-- name    : CorrColoring.ThreeChoosable.plane_precoloring_extension
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:07:32.638203+00:00
-- url     : https://prove2.me/theorems/fbc6d2df-29bd-42c5-bb31-fcc0f182b500
-- title:
--   Theorem 8 — extending precolourings of a face in plane graphs without cycles of lengths 4 to 8
-- statement:
--   Let $G$ be a finite plane graph without cycles of lengths 4 to 8. Let $S$ be a set of vertices of $G$ such that either $|S| \le 1$, or $S$ consists of all vertices incident with a face of $G$. Let $C$ be a 3-correspondence assignment for $G$ that is consistent on every closed walk of length 3 in $G$. If $|S| \le 12$, then for every $C$-coloring $\varphi_0$ of $G[S]$ there is a $C$-coloring $\varphi$ of $G$ with
--
--   $$\varphi|_S = \varphi_0 .$$
--
--   With $S = \emptyset$ this is Theorem 6; the precoloured face is what makes the statement strong enough to be proved by induction.
--
--   **Formalization Note** The plane graph is a graph with a fixed straight-line drawing $D$ (Fáry's theorem: every plane graph has one with the same faces), and the statement is made for every such drawing. Faces are connected components of the complement of the drawing and a vertex is incident with a face if its point lies in the face's closure. The face in the second alternative is any face, not only the outer one. $\varphi_0$ is a map on all vertices; only its values on $S$ matter, and it is a $C$-coloring of $G[S]$.
-- source:
--   Dvořák, Postle, Correspondence coloring and its application to list-coloring planar graphs without cycles of lengths 4 to 8, arXiv:1508.03437v2, p. 11, Theorem 8

import Mathlib
import Definitions.Def_CorrColoring_ThreeChoosable_NoCycleLengthsFourToEight
import Definitions.Def_CorrColoring_ThreeChoosable_StraightLineDrawing
import Definitions.Def_CorrColoring_ThreeChoosable_KCorrAssignment
import Definitions.Def_CorrColoring_ThreeChoosable_ConsistentOn

namespace CorrColoring.ThreeChoosable

/-- Theorem 8 (Dvořák–Postle, p. 11). -/
theorem plane_precoloring_extension {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (D : StraightLineDrawing G) (hC : NoCycleLengthsFourToEight G)
    (S : Finset V)
    (hS : S.card ≤ 1 ∨ ∃ f, D.IsFace f ∧ ∀ v, v ∈ S ↔ D.IsIncident v f)
    (C : KCorrAssignment G 3) (hcons : ConsistentOnTriangles C)
    (hS12 : S.card ≤ 12)
    (φ₀ : V → Fin 3) (hφ₀ : ∀ u v, u ∈ S → v ∈ S → G.Adj u v → ¬ C.M u (φ₀ u) v (φ₀ v)) :
    ∃ φ : V → Fin 3, IsCColoring C φ ∧ ∀ v ∈ S, φ v = φ₀ v := by sorry

end CorrColoring.ThreeChoosable
