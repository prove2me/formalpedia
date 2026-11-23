-- Prove2me | Theorems.Thm_DualityStability_StrongDuality_Supplement_theorem_5
-- name    : DualityStability.StrongDuality.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:49:14.991931+00:00
-- url     : https://prove2.me/theorems/001d260e-a393-4258-8031-b5163b522a32
-- title:
--   Theorem 5 — (P) is stably set with a solution iff (P*) is stably set with a solution
-- statement:
--   Work in the standing setting of §3, with primal problem (P), minimize $f(x)-g(Ax)$ over $x\in E$, and dual problem $(P^*)$, maximize $g^*(y^*)-f^*(A^*y^*)$ over $y^*\in F^*$.
--
--   **Theorem 5.** (P) is stably set and has a solution if and only if (P\*) is stably set and has a solution.
--
--   Here a solution to (P) satisfies the implicit constraints (3.1) and attains $\inf(P)$, and a solution to $(P^*)$ attains $\sup(P^*)$, which is then not $-\infty$. The theorem shows that the pair "stable and solvable" is symmetric between a problem and its dual.
--
--   **Formalization Note** (P\*) stably set is `StablySet p.dualH`, stability of the minimization form (P′), as in the published Theorem 3.
--
--   Differences from the source:
--   - encoding: properties of (P*) defined "in a dual manner" (pp. 173, 175, 181) → the same property of the minimization form (P′) of (P*), through its perturbation function `p.dualH` on $E^*$; reason: the paper's own dualization rule (P′), p. 173; identical to the published goal's convention
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 179, Theorem 5

import Definitions.Def_DualityStability_StrongDuality_Supplement_Solution

namespace DualityStability.StrongDuality.Supplement

open DualityStability.StrongDuality

variable {E E' F F' : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [TopologicalSpace E'] [AddCommGroup E'] [Module ℝ E']
  [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [TopologicalSpace F'] [AddCommGroup F'] [Module ℝ F']
  [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F'] [LocallyConvexSpace ℝ F'] [T2Space F']

/-- Theorem 5, p. 179: (P) is stably set and has a solution if and only if (P*) is
stably set and has a solution. -/
theorem theorem_5 (p : Program E E' F F') :
    (StablySet p.h ∧ ∃ x : E, IsPrimalSolution p x) ↔
      (StablySet p.dualH ∧ ∃ y' : F', IsDualSolution p y') := by sorry

end DualityStability.StrongDuality.Supplement
