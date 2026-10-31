-- Prove2me | Theorems.Thm_CombOpt_ShortestPath_theorem_2_12
-- name    : CombOpt.ShortestPath.theorem_2_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:04:03.977981+00:00
-- url     : https://prove2.me/theorems/3b4e75bd-5f81-4e78-bba0-a03a4a34a9ff
-- title:
--   Theorem 2.12 — $(G,c)$ has a feasible potential iff it has no negative-cost dicircuit
-- statement:
--   Let $G$ be a finite digraph (loops and parallel arcs allowed) with real arc costs $c$. Then there is a real vector $y=(y_v:v\in V)$ with
--   $$y_v+c_{vw}\ \ge\ y_w\qquad\text{for all } vw\in E$$
--   if and only if $(G,c)$ has no negative-cost dicircuit.
--
--   No reachability assumption is made: the theorem applies "even without any assumption about the existence of dipaths". Since subtracting $y_r$ from every $y_v$ preserves the inequalities, for any $r\in V$ the left side is the same as the existence of a feasible potential with root $r$.
--
--   Differences from the source:
--   - generalization: the section may assume G simple (p. 20) → loops and parallel arcs allowed; reason: every digraph of p. 19 is covered, in particular the simple ones, so the Lean statement specializes to the book's
--   - reading: "(G, c) has a feasible potential" (feasible potential: (2.12) and y_r = 0) → there is a real y satisfying (2.12), with no root fixed; reason: the theorem names no root and its proof adds a new root node; by p. 21 subtracting y_r preserves (2.12), so for every r ∈ V the two readings are equivalent
--   - encoding: a dicircuit is the sequence v_0, e_1, v_1, …, e_k, v_k → a start node and the arc list [e_1, …, e_k]; reason: the nodes are the start node and the heads of the arcs
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 2.12, p. 25 (PDF p. 34); feasible potential p. 21 (PDF p. 30)

import Mathlib
import Definitions.Def_CombOpt_ShortestPath_Digraph_SatisfiesPotentialIneq
import Definitions.Def_CombOpt_ShortestPath_Digraph_HasNegativeDicircuit

namespace CombOpt.ShortestPath

/-- **Theorem 2.12 (a feasible potential exists iff there is no negative-cost dicircuit).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 2.12, p. 25 (PDF p. 34): "(G, c) has a feasible potential if and only if it has no
negative-cost dicircuit." The book adds: "Notice that it applies even without any assumption
about the existence of dipaths."

For a finite digraph `G` with real arc costs `c`, there is a real vector `y` with
`y (head e) ≤ y (tail e) + c e` for every arc `e` (inequalities (2.12)) if and only if no
dicircuit of `G` has negative cost.

**Formalization Note.** The normalization `y_r = 0` of a feasible potential is dropped: the
theorem names no root, its proof (p. 25) adds a new node as root, and p. 21 notes that
"subtracting y_r from each y_v preserves (2.12) and makes y_r = 0", so for any `r ∈ V` the left
side is equivalent to the existence of a feasible potential with root `r`. -/
theorem theorem_2_12 {V E : Type*} [Fintype V] [Fintype E] (G : Digraph V E) (c : E → ℝ) :
    (∃ y : V → ℝ, G.SatisfiesPotentialIneq c y) ↔ ¬ G.HasNegativeDicircuit c := by sorry

end CombOpt.ShortestPath
