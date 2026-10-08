-- Prove2me | Theorems.Thm_DualityStability_StrongDuality_stable_iff_subdiff
-- name    : DualityStability.StrongDuality.stable_iff_subdiff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:43:43.366532+00:00
-- url     : https://prove2.me/theorems/9b185134-60c7-428f-8b6a-8ddd17dbb44d
-- title:
--   Proof of Theorem 3 — stability and subdifferentiability
-- statement:
--   For the perturbation function $h(z)=\inf_x\{f(x)-g(Ax-z)\}$ of the convex program in §3, the primal problem is stably set exactly when $h$ has a subgradient at zero:
--
--   $$
--   (P)\text{ is stably set}\quad\Longleftrightarrow\quad \partial h(0)\ne\varnothing.
--   $$
--
--   A subgradient is a point $y'\in F'$ satisfying $h(z)\ge h(0)+\langle z,y'\rangle_F$ for every $z\in F$. This equivalence links the paper's directional-derivative stability definition to duality. It includes the cases $h(0)=\pm\infty$ with the meanings assigned in §5.
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 178, §5, proof of Theorem 3, first claim

import Definitions.Def_DualityStability_StrongDuality_Program

namespace DualityStability.StrongDuality

variable {E E' F F' : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [TopologicalSpace E'] [AddCommGroup E'] [Module ℝ E']
  [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [TopologicalSpace F'] [AddCommGroup F'] [Module ℝ F']
  [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F'] [LocallyConvexSpace ℝ F'] [T2Space F']

/-- First claim in the proof of Theorem 3, p. 178. -/
theorem stable_iff_subdiff (p : Program E E' F F') :
    StablySet p.h ↔ (subdiff p.fPair p.h 0).Nonempty := by sorry

end DualityStability.StrongDuality
