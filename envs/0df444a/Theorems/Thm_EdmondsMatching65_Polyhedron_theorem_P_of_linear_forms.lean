-- Prove2me | Theorems.Thm_EdmondsMatching65_Polyhedron_theorem_P_of_linear_forms
-- name    : EdmondsMatching65.Polyhedron.theorem_P_of_linear_forms
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:44:17.217271+00:00
-- url     : https://prove2.me/theorems/baf4bc82-9785-47d2-8d7d-ee75095a6a45
-- title:
--   §2, p. 126 — if every linear form is maximized over C at a 0–1 point, then Theorem (P) holds
-- statement:
--   Let $G$ be a finite graph with polyhedron $C$ given by (1)–(3) and matching vectors $P$. Suppose that for every real weight vector $c\in\mathbb R^E$ there is a point $x\in C$ with all components in $\{0,1\}$ that maximizes $W(c,\cdot)=\sum_e c_e x_e$ over $C$:
--   $$\forall c\ \exists x\in C\cap\{0,1\}^E:\quad W(c,x')\le W(c,x)\ \text{ for all }x'\in C .$$
--   Then the extreme points of $C$ are exactly the matching vectors: $\operatorname{ext}(C)=P$.
--
--   This is the reduction of Theorem (P) to a statement about linear forms; the remaining milestones establish its hypothesis through linear programming duality.
--
--   **Formalization Note** The graph is given by a finite node type $V$, a finite edge type $E$ and, for each edge, the unordered pair of its ends (no loops). Parallel edges are allowed, which covers the contracted graphs of Theorem (M); a simple graph is the special case of an injective end map. Vectors $x$ have one real coordinate per edge.
-- source:
--   Edmonds, Maximum Matching and a Polyhedron With 0,1-Vertices, J. Res. NBS 69B (1965), p. 126, §2, last sentence of §2

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_EdmondsMatching65_Polyhedron_MatchingPolyhedron

namespace EdmondsMatching65.Polyhedron

theorem theorem_P_of_linear_forms {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : Graph V E)
    (h : ∀ c : E → ℝ, ∃ x ∈ matchingPolyhedron G, (∀ e, x e = 0 ∨ x e = 1) ∧
      ∀ x' ∈ matchingPolyhedron G, W c x' ≤ W c x) :
    Set.extremePoints ℝ (matchingPolyhedron G) = matchingVectors G := by sorry

end EdmondsMatching65.Polyhedron
