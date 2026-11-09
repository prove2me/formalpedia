-- Prove2me | Theorems.Thm_DelaunayStretch_theorem_3_9_potential_criterion
-- name    : DelaunayStretch.theorem_3_9_potential_criterion
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:54:12.335111+00:00
-- url     : https://prove2.me/theorems/2cfa23d7-8fe4-441a-ae74-c8c4c3a531d4
-- title:
--   Theorem 3.9 — a feasible potential of level $U\ge\pi/2$ implies the chain inequality
-- statement:
--   Let $U\ge\pi/2$. If there exists a feasible potential of level $U$, then the chain inequality holds at level $U$:
--
--   $$
--   \exists\,W\ \text{feasible of level }U\ \Longrightarrow\ P(u,v)\le U\|u-v\|\ \text{for every disk chain}.
--   $$
--
--   This reduces the chain inequality, a statement about chains of arbitrary length, to inequalities on single moves.
--
--   Differences from the source:
--   - encoding: points of ℝ² with coordinates x(z), y(z) and Euclidean norm → points of ℂ with x = re, y = im and ‖z − w‖ = dist z w; reason: ℂ is ℝ² with the Euclidean norm; same instances
--   - encoding: P(u, v), the length of a shortest path from u to v in the ladder graph → the infimum of the weights of walks from u to v in the ladder graph (vertex labels, not points); reason: the ladder graph is finite with nonnegative weights (rails by (C4) and (2.1)), so the infimum is attained and is the shortest-path length
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), Theorem 3.9, p.20

import Mathlib
import Definitions.Def_DelaunayStretch_ChainInequality
import Definitions.Def_DelaunayStretch_IsFeasiblePotential

namespace DelaunayStretch

/-- **Theorem 3.9 (Potential criterion)** (p.20). Let `U ≥ π/2`. If there exists a feasible
potential of level `U`, then the chain inequality holds at level `U`.

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026), Theorem 3.9, p.20. -/
theorem theorem_3_9_potential_criterion (U : ℝ) (hU : Real.pi / 2 ≤ U)
    (hW : ∃ W : GateState → ℝ, IsFeasiblePotential U W) : ChainInequality U := by sorry

end DelaunayStretch
