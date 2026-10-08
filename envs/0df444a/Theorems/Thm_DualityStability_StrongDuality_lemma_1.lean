-- Prove2me | Theorems.Thm_DualityStability_StrongDuality_lemma_1
-- name    : DualityStability.StrongDuality.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:44:16.079388+00:00
-- url     : https://prove2.me/theorems/246cdd97-3356-4f6d-941d-4c8b9bda6d19
-- title:
--   Lemma 1 — weak duality
-- statement:
--   For the paired-space convex program $(P)$ and its conjugate dual $(P^*)$ in §3, the dual supremum never exceeds the primal infimum:
--
--   $$
--   \sup_{y'\in F'}\{g^*(y')-f^*(A^*y')\}
--   \le \inf_{x\in E}\{f(x)-g(Ax)\}.
--   $$
--
--   Both extrema are taken in the extended reals. This inequality makes a dual point satisfying (5.1) a maximizer at the primal infimum.
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 174, Lemma 1

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

/-- Lemma 1, p. 174: weak duality. -/
theorem lemma_1 (p : Program E E' F F') : p.dualValue ≤ p.h 0 := by sorry

end DualityStability.StrongDuality
