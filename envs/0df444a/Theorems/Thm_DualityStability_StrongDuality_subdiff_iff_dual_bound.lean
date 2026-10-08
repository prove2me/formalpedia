-- Prove2me | Theorems.Thm_DualityStability_StrongDuality_subdiff_iff_dual_bound
-- name    : DualityStability.StrongDuality.subdiff_iff_dual_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:42:53.529545+00:00
-- url     : https://prove2.me/theorems/07150009-5390-4205-b73f-5cbc5e0aaf77
-- title:
--   Proof of Theorem 3 — subgradient and dual bound (5.1)
-- statement:
--   Let $h$ be the perturbation function and $f^*,g^*$ the conjugates of the convex program in §3. For every $y'\in F'$, membership in the subdifferential at zero is equivalent to inequality (5.1):
--
--   $$
--   y'\in\partial h(0)\quad\Longleftrightarrow\quad
--   \inf(P)\le g^*(y')-f^*(A^*y').
--   $$
--
--   This identifies each subgradient with a dual point whose objective reaches the primal lower bound. Combined with weak duality, it gives the attained equality in Theorem 3. The equivalence also covers the two infinite values of $\inf(P)$.
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), pp. 178–179, §5, proof of Theorem 3, (5.1)

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

/-- The equivalence (5.1) in the proof of Theorem 3, pp. 178–179. -/
theorem subdiff_iff_dual_bound (p : Program E E' F F') (y' : F') :
    y' ∈ subdiff p.fPair p.h 0 ↔ p.h 0 ≤ p.dualAt y' := by sorry

end DualityStability.StrongDuality
