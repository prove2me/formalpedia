-- Prove2me | Theorems.Thm_EdmondsMatching65_Polyhedron_exists_certificate
-- name    : EdmondsMatching65.Polyhedron.exists_certificate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:43:29.686981+00:00
-- url     : https://prove2.me/theorems/d1a111a4-ceaf-4687-b22b-3ca76e090cec
-- title:
--   §3, pp. 127–128 — for every weight vector, a matching M and ⟨y, z⟩₀ satisfying (6)–(10)
-- statement:
--   Let $G$ be a finite graph. For every real weight vector $c\in\mathbb R^E$ there exist a matching $M$ of $G$ and a dual vector $\langle y,z\rangle$ which satisfies the dual inequalities (6) and (7) and, relative to $M$, the conditions (8), (9) and (10).
--
--   With weak duality and the equality $U=W$ under (6)–(10), this shows that every linear form $W$ is maximized over $C$ by a matching vector, which by the reduction of §2 gives Theorem (P).
--
--   **Formalization Note** The graph is given by a finite node type $V$, a finite edge type $E$ and, for each edge, the unordered pair of its ends (no loops). Parallel edges are allowed, which covers the contracted graphs of Theorem (M); a simple graph is the special case of an injective end map. Vectors $x$ have one real coordinate per edge.
-- source:
--   Edmonds, Maximum Matching and a Polyhedron With 0,1-Vertices, J. Res. NBS 69B (1965), p. 127, §3, paragraph before (8); conclusion p. 128, end of §5

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_EdmondsMatching65_Polyhedron_DualProgram

namespace EdmondsMatching65.Polyhedron

theorem exists_certificate {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : Graph V E) (c : E → ℝ) :
    ∃ M : Finset E, IsMatching G M ∧
      ∃ (y : V → ℝ) (z : Finset V → ℝ), DualFeasible G c y z ∧ CompSlack G c M y z := by sorry

end EdmondsMatching65.Polyhedron
