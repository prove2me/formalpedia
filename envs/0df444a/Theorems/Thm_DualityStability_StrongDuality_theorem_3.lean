-- Prove2me | Theorems.Thm_DualityStability_StrongDuality_theorem_3
-- name    : DualityStability.StrongDuality.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:43:43.095634+00:00
-- url     : https://prove2.me/theorems/3cac9b59-c64e-4398-ae69-80db4c327ee0
-- title:
--   Theorem 3 — stable setting and attained strong duality
-- statement:
--   Under the standing paired-space, adjoint, and proper semicontinuous convex–concave hypotheses of §3, stability of the primal problem is equivalent to equality of its infimum with an **attained** dual maximum. Dually, equality of an attained primal minimum with the dual supremum is equivalent to stability of the dual problem, understood through its minimization form $(P')$:
--
--   $$
--   (P)\text{ is stably set}\quad\Longleftrightarrow\quad
--   \inf(P)=\max(P^*),
--   $$
--   $$
--   \min(P)=\sup(P^*)\quad\Longleftrightarrow\quad
--   (P^*)\text{ is stably set}.
--   $$
--
--   Here $\max(P^*)$ and $\min(P)$ assert attainment as well as equality. This characterizes when perturbation stability supplies strong duality and a dual optimizer, and gives the symmetric primal-attainment statement.
--
--   **Formalization Note** Both extrema and the values of $f,g$ lie in the extended reals. Stability is defined by the directional derivative of the perturbation function, not by subgradient existence. The second stability condition is applied to $(P')$, whose perturbations lie in $E'$. The case $\inf(P)=-\infty$ remains included; the dual maximum then has value $-\infty$.
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 178, Theorem 3

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

/-- Theorem 3, p. 178: stable setting is equivalent to attained strong duality;
the dual statement is obtained by stability of the reformulated dual problem (P'). -/
theorem theorem_3 (p : Program E E' F F') :
    (StablySet p.h ↔ IsGreatest (Set.range p.dualAt) (p.h 0)) ∧
    (IsLeast (Set.range (p.primalAt 0)) p.dualValue ↔ StablySet p.dualH) := by sorry

end DualityStability.StrongDuality
