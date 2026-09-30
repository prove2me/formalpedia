-- Prove2me | Theorems.Thm_CorrColoring_ThreeChoosable_minimal_counterexample_triangle_full
-- name    : CorrColoring.ThreeChoosable.minimal_counterexample_triangle_full
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:06:17.731971+00:00
-- url     : https://prove2.me/theorems/6c639d5f-e74e-4a27-9704-ad42539c8016
-- title:
--   Lemma 11 — triangles with two degree-3 vertices outside $S$ are full
-- statement:
--   Let $B = (G, S, C, \varphi_0)$ be a minimal counterexample and let $T = abc$ be a triangle of $G$ with at least two vertices of degree three not belonging to $S$, say $a$ and $b$. Then
--
--   $$\text{the edges } ab,\ bc,\ ca \text{ are all full in } C .$$
--
--   The triangles of this kind are those appearing in the tetrads of Lemma 12.
--
--   **Formalization Note** The triangle is given by three pairwise adjacent vertices $a, b, c$, with $a$ and $b$ the two vertices of degree three outside $S$ (any triangle with at least two such vertices can be labelled this way). The degree is the cardinality of the neighbour set. As in the paper, the hypothesis describes a hypothetical object.
-- source:
--   Dvořák, Postle, Correspondence coloring and its application to list-coloring planar graphs without cycles of lengths 4 to 8, arXiv:1508.03437v2, p. 15, Lemma 11

import Mathlib
import Definitions.Def_CorrColoring_ThreeChoosable_Straight
import Definitions.Def_CorrColoring_ThreeChoosable_Target

namespace CorrColoring.ThreeChoosable

/-- Lemma 11 (Dvořák–Postle, p. 15). -/
theorem minimal_counterexample_triangle_full (B : Target) (hB : B.IsMinimalCounterexample)
    (a b c : B.V) (hab : B.G.Adj a b) (hbc : B.G.Adj b c) (hca : B.G.Adj c a)
    (ha : (B.G.neighborSet a).ncard = 3 ∧ a ∉ B.S)
    (hb : (B.G.neighborSet b).ncard = 3 ∧ b ∉ B.S) :
    Full B.C a b ∧ Full B.C b c ∧ Full B.C c a := by sorry

end CorrColoring.ThreeChoosable
