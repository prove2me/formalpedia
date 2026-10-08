-- Prove2me | Theorems.Thm_DualityStability_WeakDuality_improper_case
-- name    : DualityStability.WeakDuality.improper_case
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:44:32.92963+00:00
-- url     : https://prove2.me/theorems/49fc5a1d-446e-4b4d-adc5-f99264611759
-- title:
--   §6, p. 180 — if h̄ is not proper, the maximand of (P*) is identically −∞
-- statement:
--   In the setting of the dual programs (P) and (P\*), let $h(z)=\inf(\mathrm P(z))$ and let $\bar h(y)=\liminf_{z\to y}h(z)$ be its lower semicontinuous hull. If $\bar h$ is not proper, that is, $\bar h(y)=-\infty$ for some $y$ or $\bar h(y)=+\infty$ for every $y$, then
--   $$g^*(y^*)-f^*(A^*y^*)=-\infty\qquad\text{for every }y^*\in F^*,$$
--   so the maximand of (P\*) is identically $-\infty$ and $\sup(\mathrm P^*)=-\infty$.
--
--   The statement includes the claim that $\bar h$ is not identically $+\infty$ under the standing hypotheses; in that case the maximand would be identically $+\infty$. This is the improper case of the proof of Theorem 6.
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 180, §6, proof of Theorem 6 (improper case)

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

/-- Rockafellar 1967, §6, p. 180, proof of Theorem 6: if the l.s.c. hull `h̄` is not proper,
then the maximand `g*(y*) - f*(A*y*)` of (P*) is identically `-∞`. -/
theorem improper_case (P : Problem E E' F F')
    (himproper : ¬ Proper P.hull) :
    ∀ y' : F', P.dualMaximand y' = ⊥ := by sorry

end DualityStability.WeakDuality
