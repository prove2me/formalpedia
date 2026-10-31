-- Prove2me | Theorems.Thm_CombOpt_ShortestPath_theorem_2_14
-- name    : CombOpt.ShortestPath.theorem_2_14
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:03:30.816562+00:00
-- url     : https://prove2.me/theorems/2872caa3-19b7-422a-8ebd-a8785496efa7
-- title:
--   Theorem 2.14 — min dipath cost from $r$ to $s$ equals max $y_s$ over feasible potentials
-- statement:
--   Let $G$ be a finite digraph (loops and parallel arcs allowed), $r,s\in V$, and $c\in\mathbb R^E$. Suppose that for every $v\in V$ there exists a least-cost dipath from $r$ to $v$. Then
--   $$\min\{c(P): P\text{ a dipath from } r \text{ to } s\}\;=\;\max\{y_s : y\text{ a feasible potential}\},$$
--   where dipaths may repeat nodes and arcs, and a feasible potential is a real vector $y$ with $y_v+c_{vw}\ge y_w$ for all $vw\in E$ and $y_r=0$. Both the minimum and the maximum are attained.
--
--   The maximization is a linear program, (2.13), whose dual (2.14) is a minimum-cost flow formulation of the shortest $r$–$s$ dipath problem; the theorem is the combinatorial form of linear-programming duality for this pair.
--
--   Differences from the source:
--   - generalization: the section may assume G simple (p. 20) → loops and parallel arcs allowed; reason: every digraph of p. 19 is covered, in particular the simple ones, so the Lean statement specializes to the book's
--   - encoding: min{…} = max{…} → there is a real m that is the least element of the set of dipath costs and the greatest element of the set of values y_s; reason: this asserts that both optima are attained and are equal, which is what the book's min and max mean
--   - encoding: a dipath is the sequence v_0, e_1, v_1, …, e_k, v_k → a start node and the arc list [e_1, …, e_k]; reason: the nodes are the start node and the heads of the arcs
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 2.14, p. 26 (PDF p. 35)

import Mathlib
import Definitions.Def_CombOpt_ShortestPath_Digraph_IsLeastCostDipath
import Definitions.Def_CombOpt_ShortestPath_Digraph_IsFeasiblePotential
import Definitions.Def_CombOpt_ShortestPath_pathCost

namespace CombOpt.ShortestPath

/-- **Theorem 2.14 (least dipath cost equals the largest feasible potential value).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 2.14, p. 26 (PDF p. 35): "Let G be a digraph, r, s ∈ V and c ∈ R^E. If there
exists a least-cost dipath from r to v for every v ∈ V, then
  min{c(P) : P a dipath from r to s} = max{y_s : y a feasible potential}."

For a finite digraph `G`, nodes `r, s` and real arc costs `c`, if every node `v` has a
least-cost dipath from `r` (a dipath from `r` to `v` whose cost is at most that of every
dipath from `r` to `v`), then there is a real number `m` that is the least element of the
set of costs of all dipaths from `r` to `s` (nodes and arcs may repeat) and the greatest
element of the set of values `y s` over all feasible potentials `y` (root `r`).

**Formalization Note.** The two sides of the book's equation are `IsLeast` and
`IsGreatest` of the same real number, so both the minimum and the maximum are asserted to be
attained. -/
theorem theorem_2_14 {V E : Type*} [Fintype V] [Fintype E] (G : Digraph V E) (c : E → ℝ)
    (r s : V) (h : ∀ v : V, ∃ P : List E, G.IsLeastCostDipath c r v P) :
    ∃ m : ℝ,
      IsLeast {x : ℝ | ∃ P : List E, G.IsDipath r P s ∧ x = pathCost c P} m ∧
      IsGreatest {x : ℝ | ∃ y : V → ℝ, G.IsFeasiblePotential c r y ∧ x = y s} m := by sorry

end CombOpt.ShortestPath
