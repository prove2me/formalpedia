-- Prove2me | Theorems.Thm_DelaunayStretch_theorem_4_7_sufficient_conditions
-- name    : DelaunayStretch.theorem_4_7_sufficient_conditions
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:56:55.157499+00:00
-- url     : https://prove2.me/theorems/b036a994-0941-4595-91d2-a29731ecff98
-- title:
--   Theorem 4.7 — (H0)–(H4) at level $U\ge\pi/2$ make $W_{H,U}$ a feasible potential, so the chain inequality holds
-- statement:
--   Let $U\ge\pi/2$, and let $H$ be a real function on $\Omega\times\mathbb R$ that satisfies (H0)–(H4) at level $U$. Then $W_{H,U}$ is a feasible potential of level $U$. Consequently, the chain inequality holds at level $U$.
--
--   $$
--   \text{(H0)–(H4) at level }U\ \Longrightarrow\ W_{H,U}\ \text{feasible}\ \Longrightarrow\ P(u,v)\le U\|u-v\|\ \text{for every disk chain}.
--   $$
--
--   This reduces the nine-parameter inequalities of a feasible potential to conditions on one function of four angles.
--
--   Differences from the source:
--   - encoding: points of ℝ² with coordinates x(z), y(z) and Euclidean norm → points of ℂ with x = re, y = im and ‖z − w‖ = dist z w; reason: ℂ is ℝ² with the Euclidean norm; same instances
--   - encoding: H a real function on Ω × ℝ → H : ℝ⁴ → ℝ, z = (γ, φ, θ, ψ); every hypothesis and conclusion reads H only on Ω × ℝ (on Σ for gate states); reason: Ω × ℝ is open in ℝ⁴, so values and derivatives of H there do not depend on the values outside; same functions
--   - encoding: P(u, v), the length of a shortest path from u to v in the ladder graph → the infimum of the weights of walks from u to v in the ladder graph (vertex labels, not points); reason: the ladder graph is finite with nonnegative weights (rails by (C4) and (2.1)), so the infimum is attained and is the shortest-path length
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), Theorem 4.7, p.27

import Mathlib
import Definitions.Def_DelaunayStretch_ChainInequality
import Definitions.Def_DelaunayStretch_IsFeasiblePotential
import Definitions.Def_DelaunayStretch_SatisfiesH0toH4

namespace DelaunayStretch

/-- **Theorem 4.7 (Sufficient conditions)** (p.27). Let `U ≥ π/2`, and let `H` be a real
function on `Ω × ℝ` that satisfies (H0)–(H4) at level `U`. Then `W_{H,U}` is a feasible
potential of level `U`. Consequently, the chain inequality holds at level `U`.

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026), Theorem 4.7, p.27. -/
theorem theorem_4_7_sufficient_conditions (U : ℝ) (hU : Real.pi / 2 ≤ U) (H : R4 → ℝ)
    (hH : SatisfiesH0toH4 U H) :
    IsFeasiblePotential U (potential H U) ∧ ChainInequality U := by sorry

end DelaunayStretch
