-- Prove2me | Theorems.Thm_ContPatrol_theorem_3
-- name    : ContPatrol.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:32.604988+00:00
-- url     : https://prove2.me/theorems/acd30d72-26c8-4717-a807-c665df5c572e
-- title:
--   Theorem 3: every network has a double tour reversing only at leaf nodes
-- statement:
--   For any network $Q$ there is a tour $S_2$ which covers every arc twice and for which no arc is traversed consecutively in opposite directions, except for leaf arcs.
--
--   The tour $S_2$ is the trajectory of the Patroller's optimal strategy $S_2^\alpha$ in Theorem 6.
--
--   **Formalization Note** The tour is a closed dart walk (first dart $d$ followed by the list $ds$) in which every edge occurs exactly twice and a dart is followed by its reverse only at a vertex of degree $1$.
--
--   Differences from the source:
--   - encoding: a network Q: a connected graph with positive arc lengths, viewed as a metric space; nodes are the points of degree ≠ 2; the line segment is excluded → MetricGraph V E with IsNetwork: finite types of vertices and edges, src/tgt maps (loops and parallel edges allowed), len e > 0, Nonempty E, connected, and (∃ v, 3 ≤ deg v) ∨ (∀ v, deg v ≠ 1); vertices of degree 2 allowed; points are vertices or interior points of edges; reason: a subdivided arc is the same metric space; every network arises this way, and leaf arcs, girth and reversals are defined subdivision-invariantly
--   - encoding: no arc is traversed consecutively in opposite directions, except for leaf arcs → a dart followed (cyclically) by its own reverse only when the vertex between them has degree 1; reason: the walk can reverse inside a leaf arc only at its leaf node; degree-2 vertices are interior points of arcs
-- source:
--   Alpern, Bui, Lidbetter, Papadaki, Continuous Patrolling Games, arXiv:2008.07369v2, Theorem 3, p.11

import Mathlib
import Definitions.Def_ContPatrol_MetricGraph_IsNetwork
import Definitions.Def_ContPatrol_Multigraph_IsDoubleTour

namespace ContPatrol

open MetricGraph

/-- **Theorem 3** (Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*, arXiv:2008.07369v2, Theorem 3, p.11):
"For any network Q there is a tour S2 which covers every arc twice and for which no arc is
traversed consecutively in opposite directions, except for leaf arcs."

Every network has a closed dart walk `d :: ds` that uses every edge exactly twice and reverses
direction only at leaf nodes (`Multigraph.IsDoubleTour`). -/
theorem theorem_3 {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : MetricGraph V E) (hG : G.IsNetwork) :
    ∃ (d : E × Bool) (ds : List (E × Bool)), G.IsDoubleTour (d :: ds) := by sorry

end ContPatrol
