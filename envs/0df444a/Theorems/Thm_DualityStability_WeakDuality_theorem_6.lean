-- Prove2me | Theorems.Thm_DualityStability_WeakDuality_theorem_6
-- name    : DualityStability.WeakDuality.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:44:38.481984+00:00
-- url     : https://prove2.me/theorems/775aa156-e8fa-4a20-9766-b845f1e31456
-- title:
--   Theorem 6 — sup (P*) = lim inf_{z→0} [inf (P(z))], except when the left side is −∞ and the right side +∞
-- statement:
--   Let $(E,E^*)$ and $(F,F^*)$ be topologically paired real vector spaces, $A:E\to F$ continuous linear with adjoint $A^*:F^*\to E^*$, $f:E\to[-\infty,+\infty]$ lower semicontinuous proper convex, and $g:F\to[-\infty,+\infty]$ upper semicontinuous proper concave, with conjugates $f^*$ and $g^*$. Consider the primal problem (P), minimize $f(x)-g(Ax)$ over $x\in E$; its perturbations (P($z$)), minimize $f(x)-g(Ax-z)$, for $z\in F$; and the dual problem (P\*), maximize $g^*(y^*)-f^*(A^*y^*)$ over $y^*\in F^*$. Then
--   $$\sup(\mathrm P^*)=\liminf_{z\to0}\,[\inf(\mathrm P(z))],$$
--   except in the trivial case where the left side is $-\infty$ and the right side is $+\infty$.
--
--   This is the weak duality theorem of the paper. It explains exactly how $\inf(\mathrm P)$ and $\sup(\mathrm P^*)$ can fail to be equal, by expressing $\sup(\mathrm P^*)$ through the behaviour of the perturbed problems (P) itself: the duality gap is the gap between $\inf(\mathrm P(0))$ and its lower limit as $z\to0$. No consistency, constraint qualification or attainment is assumed.
--
--   **Formalization Note** The lower limit is `Filter.liminf (fun z => inf (P(z))) (nhds 0)`, over the full neighbourhood filter of $0$, so $z=0$ is included. The exception is the conjunction "$\sup(\mathrm P^*)=-\infty$ and the lower limit is $+\infty$", exactly as printed. The dual value is computed from $f^*$, $g^*$ and $A^*$, not from the perturbation function.
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), pp. 179–180, Theorem 6

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

/-- Rockafellar 1967, Theorem 6, pp. 179–180: `sup (P*) = lim inf_{z → 0} [inf (P(z))]`,
except in the trivial case where the left side is `-∞` and the right side `+∞`. -/
theorem theorem_6 (P : Problem E E' F F')
    (hexception : ¬ (P.dualSup = ⊥ ∧ Filter.liminf P.perturbation (nhds 0) = ⊤)) :
    P.dualSup = Filter.liminf P.perturbation (nhds 0) := by sorry

end DualityStability.WeakDuality
