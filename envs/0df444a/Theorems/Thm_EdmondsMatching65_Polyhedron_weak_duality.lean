-- Prove2me | Theorems.Thm_EdmondsMatching65_Polyhedron_weak_duality
-- name    : EdmondsMatching65.Polyhedron.weak_duality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:44:34.038983+00:00
-- url     : https://prove2.me/theorems/ede43cf0-fc92-4c8e-b239-15f35c043986
-- title:
--   §3, p. 126 — weak duality: W ≤ U for every x in C and every ⟨y, z⟩ satisfying (6)–(7)
-- statement:
--   Let $G$ be a finite graph with edge weights $c\in\mathbb R^E$. If $x$ satisfies (1)–(3), i.e. $x\in C$, and $\langle y,z\rangle$ satisfies the dual inequalities (6) and (7), then
--   $$W(c,x)=\sum_{e\in E}c_e x_e\ \le\ \sum_{v\in V}y_v+\sum_{S\text{ odd}}r_S z_S=U(y,z).$$
--
--   This is the easy half of linear programming duality for the pair $(C,W)$ and $(U,(6)	ext{–}(7))$: a dual feasible vector bounds the value of $W$ over the whole polyhedron $C$.
--
--   **Formalization Note** The graph is given by a finite node type $V$, a finite edge type $E$ and, for each edge, the unordered pair of its ends (no loops). Parallel edges are allowed, which covers the contracted graphs of Theorem (M); a simple graph is the special case of an injective end map. Vectors $x$ have one real coordinate per edge.
-- source:
--   Edmonds, Maximum Matching and a Polyhedron With 0,1-Vertices, J. Res. NBS 69B (1965), p. 126, §3, paragraph after (7)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_EdmondsMatching65_Polyhedron_MatchingPolyhedron
import Definitions.Def_EdmondsMatching65_Polyhedron_DualProgram

namespace EdmondsMatching65.Polyhedron

theorem weak_duality {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : Graph V E) (c x : E → ℝ) (y : V → ℝ) (z : Finset V → ℝ)
    (hx : x ∈ matchingPolyhedron G) (hyz : DualFeasible G c y z) :
    W c x ≤ U y z := by sorry

end EdmondsMatching65.Polyhedron
