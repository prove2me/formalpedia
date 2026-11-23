-- Prove2me | Theorems.Thm_DualityStability_StrongDuality_Supplement_theorem_8
-- name    : DualityStability.StrongDuality.Supplement.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:52:10.340233+00:00
-- url     : https://prove2.me/theorems/36117ff8-7b83-4e56-b5fe-aec26df2ecaa
-- title:
--   Theorem 8 — (P), (P*) stably set iff the extremality conditions are solvable; then solution pairs are exactly extremality pairs
-- statement:
--   Work in the standing setting of §3. The extremality conditions (8.5) for $x\in E$, $y^*\in F^*$ are
--
--   $$
--   Ax\in\partial g^*(y^*)\quad\text{and}\quad A^*y^*\in\partial f(x),
--   $$
--
--   with $\partial f$ the sub-differential (2.3) of the convex function $f$ and $\partial g^*$ the sub-differential of the concave function $g^*$ ($y\in\partial g^*(y^*)$ iff $g^*(y^*+w)\le g^*(y^*)+\langle y,w\rangle$ for all $w$).
--
--   **Theorem 8.**
--
--   1. (P) and $(P^*)$ are both stably set if and only if the extremality conditions can be satisfied by some pair $(x,y^*)$.
--   2. In that case, for all $\bar x\in E$ and $\bar y^*\in F^*$: $\bar x$ is a solution to (P) and $\bar y^*$ is a solution to $(P^*)$ if and only if $\bar x$ and $\bar y^*$ satisfy the extremality conditions.
--
--   For dual linear programs the extremality conditions reduce to complementary slackness.
--
--   **Formalization Note** (P\*) stably set is `StablySet p.dualH`, as in the published Theorem 3.
--
--   Differences from the source:
--   - encoding: properties of (P*) defined "in a dual manner" (pp. 173, 175, 181) → the same property of the minimization form (P′) of (P*), through its perturbation function `p.dualH` on $E^*$; reason: the paper's own dualization rule (P′), p. 173; identical to the published goal's convention
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 184, Theorem 8 and (8.5)

import Definitions.Def_DualityStability_StrongDuality_Supplement_Solution
import Definitions.Def_DualityStability_StrongDuality_Supplement_Extremality

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

/-- Theorem 8, p. 184: (P) and (P*) are stably set iff the extremality conditions can be
satisfied; in that case `x̄` solves (P) and `ȳ*` solves (P*) iff they satisfy the
extremality conditions. -/
theorem theorem_8 (p : Program E E' F F') :
    ((StablySet p.h ∧ StablySet p.dualH) ↔ ∃ (x : E) (y' : F'), Extremal p x y') ∧
      ((StablySet p.h ∧ StablySet p.dualH) →
        ∀ (xb : E) (yb : F'),
          (IsPrimalSolution p xb ∧ IsDualSolution p yb) ↔ Extremal p xb yb) := by sorry

end DualityStability.StrongDuality.Supplement
