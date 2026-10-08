-- Prove2me | Theorems.Thm_EdmondsMatching65_Polyhedron_W_eq_U_of_compSlack
-- name    : EdmondsMatching65.Polyhedron.W_eq_U_of_compSlack
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:44:43.902988+00:00
-- url     : https://prove2.me/theorems/8d78987d-3d96-4bab-bfa5-44ea30bdbe34
-- title:
--   §3, p. 127 — under (6)–(10), the matching vector and ⟨y, z⟩ give U = W
-- statement:
--   Let $G$ be a finite graph with edge weights $c$, let $M$ be a matching with incidence vector $\chi^M$, and let $\langle y,z\rangle$ satisfy the dual inequalities (6) and (7) together with the conditions (8), (9) and (10) relative to $M$. Then
--   $$W(c,\chi^M)=\sum_{e\in M}c_e=U(y,z).$$
--
--   Combined with weak duality, this shows that such a matching vector maximizes $W$ over the whole polyhedron $C$.
--
--   **Formalization Note** The graph is given by a finite node type $V$, a finite edge type $E$ and, for each edge, the unordered pair of its ends (no loops). Parallel edges are allowed, which covers the contracted graphs of Theorem (M); a simple graph is the special case of an injective end map. Vectors $x$ have one real coordinate per edge.
-- source:
--   Edmonds, Maximum Matching and a Polyhedron With 0,1-Vertices, J. Res. NBS 69B (1965), p. 127, §3, (8)–(10) and the sentence after them

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_EdmondsMatching65_Polyhedron_MatchingPolyhedron
import Definitions.Def_EdmondsMatching65_Polyhedron_DualProgram

namespace EdmondsMatching65.Polyhedron

theorem W_eq_U_of_compSlack {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : Graph V E) (c : E → ℝ) (M : Finset E) (y : V → ℝ)
    (z : Finset V → ℝ) (hM : IsMatching G M) (hyz : DualFeasible G c y z)
    (hcs : CompSlack G c M y z) :
    W c (incidence M) = U y z := by sorry

end EdmondsMatching65.Polyhedron
