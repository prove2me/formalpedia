-- Prove2me | Theorems.Thm_DualityStability_WeakDuality_hull_lsc_convex
-- name    : DualityStability.WeakDuality.hull_lsc_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:44:18.8182+00:00
-- url     : https://prove2.me/theorems/daa8b509-79bc-4bf6-aa6c-24100cf371ac
-- title:
--   §6, p. 180 — the l.s.c. hull of inf (P(z)) is a l.s.c. convex function on F
-- statement:
--   In the setting of the dual programs (P) and (P\*), let $h(z)=\inf(\mathrm P(z))=\inf_x\{f(x)-g(Ax-z)\}$ for $z\in F$, and let $\bar h$ be the lower semicontinuous hull of $h$,
--   $$\bar h(y)=\liminf_{z\to y}h(z)\qquad(y\in F).$$
--   Then $\bar h$ is a lower semicontinuous convex function on $F$: it is lower semicontinuous, and its epigraph $\{(y,\mu)\mid\mu\in\mathbb R,\ \mu\ge\bar h(y)\}$ is a convex subset of $F\times\mathbb R$.
--
--   This is the first step of the proof of Theorem 6. It places $\bar h$ in the class of functions to which conjugate duality applies, whether or not $\bar h$ is proper.
--
--   **Formalization Note** $\bar h$ may take the values $\pm\infty$; convexity is epigraph convexity. The lower limit includes $z=y$.
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 180, §6, proof of Theorem 6 (first paragraph)

import Definitions.Def_DualityStability_WeakDuality_Problem

namespace DualityStability.WeakDuality

variable {E E' F F' : Type*}
variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
variable [AddCommGroup E'] [Module ℝ E'] [TopologicalSpace E']
  [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
variable [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
variable [AddCommGroup F'] [Module ℝ F'] [TopologicalSpace F']
  [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F'] [LocallyConvexSpace ℝ F'] [T2Space F']

/-- Rockafellar 1967, §6, p. 180, proof of Theorem 6: the l.s.c. hull
`h̄(y) = lim inf_{z → y} h(z)` of `h(z) = inf (P(z))` is a lower semicontinuous convex
(epigraph-convex) function on `F`. -/
theorem hull_lsc_convex (P : Problem E E' F F') :
    LowerSemicontinuous P.hull ∧ EpigraphConvex P.hull := by sorry

end DualityStability.WeakDuality
