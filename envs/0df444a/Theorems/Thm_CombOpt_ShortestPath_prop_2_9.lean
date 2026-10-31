-- Prove2me | Theorems.Thm_CombOpt_ShortestPath_prop_2_9
-- name    : CombOpt.ShortestPath.prop_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:03:35.021353+00:00
-- url     : https://prove2.me/theorems/993c974b-0aba-423a-8063-09a90d84bba5
-- title:
--   Proposition 2.9 — a feasible potential bounds every dipath cost from below
-- statement:
--   Let $G=(V,E)$ be a finite digraph (loops and parallel arcs allowed) with real arc costs $c=(c_e:e\in E)$ and root $r\in V$. Let $y$ be a feasible potential, i.e. $y_v+c_{vw}\ge y_w$ for every arc $vw$ and $y_r=0$, and let $P$ be a dipath from $r$ to $v$ (nodes and arcs may repeat). Then
--   $$c(P)\ \ge\ y_v .$$
--
--   Feasible potentials therefore certify lower bounds for shortest path costs: a feasible potential $y$ together with dipaths of cost $y_v$ proves that these dipaths are least-cost.
--
--   Differences from the source:
--   - generalization: the section assumes that dipaths exist from r to all the nodes and may assume G simple (p. 20) → neither assumption; loops and parallel arcs allowed; reason: the Lean statement covers every digraph of p. 19, in particular the book's
--   - encoding: a dipath is the sequence v_0, e_1, v_1, …, e_k, v_k → a start node and the arc list [e_1, …, e_k] with `IsDipath`; reason: the nodes are the start node and the heads of the arcs, so each dipath has exactly one representation
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Proposition 2.9, p. 21 (PDF p. 30)

import Mathlib
import Definitions.Def_CombOpt_ShortestPath_Digraph_IsFeasiblePotential
import Definitions.Def_CombOpt_ShortestPath_Digraph_IsDipath
import Definitions.Def_CombOpt_ShortestPath_pathCost

namespace CombOpt.ShortestPath

/-- **Proposition 2.9 (feasible potentials bound dipath costs).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Proposition 2.9, p. 21 (PDF p. 30): "Let y be a feasible potential and let P be a dipath
from r to v. Then c(P) ≥ y_v."

For a finite digraph `G` with real arc costs `c` and root `r`, every feasible potential `y`
(`y` satisfies (2.12) and `y r = 0`) and every dipath `P` from `r` to `v` (nodes and arcs
may repeat) satisfy `y v ≤ c(P)`. -/
theorem prop_2_9 {V E : Type*} [Fintype V] [Fintype E] (G : Digraph V E) (c : E → ℝ) (r : V)
    (y : V → ℝ) (hy : G.IsFeasiblePotential c r y) (v : V) (P : List E)
    (hP : G.IsDipath r P v) :
    y v ≤ pathCost c P := by sorry

end CombOpt.ShortestPath
