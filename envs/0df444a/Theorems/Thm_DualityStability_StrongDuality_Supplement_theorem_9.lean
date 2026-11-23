-- Prove2me | Theorems.Thm_DualityStability_StrongDuality_Supplement_theorem_9
-- name    : DualityStability.StrongDuality.Supplement.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:54:09.283766+00:00
-- url     : https://prove2.me/theorems/18fb427e-d8e7-4ad0-8339-5964d4b0c067
-- title:
--   Theorem 9 — the Kuhn–Tucker function has a saddle-point iff (P), (P*) are stably set; saddle-points are the solution pairs; minimax $K=\min(P)=\max(P^*)$
-- statement:
--   Work in the standing setting of §3, with $C=\operatorname{dom}f$, $D^*=\operatorname{dom}g^*$ and the Kuhn–Tucker function
--
--   $$
--   K(x,y^*)=f(x)+g^*(y^*)-\langle Ax,y^*\rangle,\qquad (x,y^*)\in C\times D^*.
--   $$
--
--   A saddle-point is a pair $(\bar x,\bar y^*)\in C\times D^*$ with $K(\bar x,\bar y^*)=\min_{x\in C}K(x,\bar y^*)=\max_{y^*\in D^*}K(\bar x,y^*)$, and $K(\bar x,\bar y^*)$ is then the minimax of $K$.
--
--   **Theorem 9.**
--
--   1. $K$ has a saddle-point if and only if (P) and $(P^*)$ are stably set.
--   2. In that case, $(\bar x,\bar y^*)$ is a saddle-point of $K$ if and only if $\bar x$ is a solution to (P) and $\bar y^*$ is a solution to $(P^*)$.
--   3. Then, for every saddle-point,
--   $$
--   \text{minimax }K=\min(P)=\max(P^*). \tag{9.2}
--   $$
--
--   This is the minimax (Lagrangian) characterization of the duality theory.
--
--   **Formalization Note** $K$ is an `EReal`-valued expression that is finite on $C\times D^*$; the saddle-point condition evaluates it only there. In part 3, attainment of $\min(P)$ and $\max(P^*)$ is part 2; the Lean conclusion records the equalities $K(\bar x,\bar y^*)=\inf(P)=\sup(P^*)$. (P\*) stably set is `StablySet p.dualH`.
--
--   Differences from the source:
--   - encoding: properties of (P*) defined "in a dual manner" (pp. 173, 175, 181) → the same property of the minimization form (P′) of (P*), through its perturbation function `p.dualH` on $E^*$; reason: the paper's own dualization rule (P′), p. 173; identical to the published goal's convention
--   - encoding: K finite-valued on C × D* → `EReal`-valued K on E × F*, with every saddle-point quantifier restricted to C and D*; reason: K is only evaluated on C × D*, where the EReal value is the paper's real number
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 186, Theorem 9; p. 185, (9.1)

import Definitions.Def_DualityStability_StrongDuality_Supplement_Solution
import Definitions.Def_DualityStability_StrongDuality_Supplement_KuhnTucker

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

/-- Theorem 9, p. 186: the Kuhn–Tucker function has a saddle-point iff (P) and (P*) are
stably set; in that case the saddle-points are exactly the pairs of solutions, and
(9.2) `minimax K = min (P) = max (P*)`. -/
theorem theorem_9 (p : Program E E' F F') :
    ((∃ (xb : E) (yb : F'), IsSaddlePoint p xb yb) ↔
        (StablySet p.h ∧ StablySet p.dualH)) ∧
      ((StablySet p.h ∧ StablySet p.dualH) →
        ∀ (xb : E) (yb : F'),
          IsSaddlePoint p xb yb ↔ (IsPrimalSolution p xb ∧ IsDualSolution p yb)) ∧
      ((StablySet p.h ∧ StablySet p.dualH) →
        ∀ (xb : E) (yb : F'), IsSaddlePoint p xb yb →
          kuhnTucker p xb yb = p.h 0 ∧ kuhnTucker p xb yb = p.dualValue) := by sorry

end DualityStability.StrongDuality.Supplement
