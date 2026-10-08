-- Prove2me | Theorems.Thm_DualityStability_WeakDuality_biconjugation_at_zero
-- name    : DualityStability.WeakDuality.biconjugation_at_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:44:44.927613+00:00
-- url     : https://prove2.me/theorems/e116e85d-1350-4429-92c6-dec1e3bf1642
-- title:
--   (6.2), p. 180 — for proper h̄, h̄(0) = sup_{y*} {⟨0, y*⟩ − h̄*(y*)}
-- statement:
--   In the setting of the dual programs (P) and (P\*), let $h(z)=\inf(\mathrm P(z))$, let $\bar h(y)=\liminf_{z\to y}h(z)$ be its lower semicontinuous hull, and let $\bar h^*(y^*)=\sup_y\{\langle y,y^*\rangle-\bar h(y)\}$ for $y^*\in F^*$. If $\bar h$ is proper ($\bar h(y)>-\infty$ for every $y$ and $\bar h(y)<+\infty$ for some $y$), then
--   $$\bar h(0)=\sup_{y^*\in F^*}\{\langle 0,y^*\rangle-\bar h^*(y^*)\}.$$
--
--   This is the equation (6.2) of the paper: since $\bar h$ is in turn the conjugate of $\bar h^*$, its value at $0$ is recovered from $\bar h^*$. It is the proper case of the proof of Theorem 6.
--
--   **Formalization Note** The term $\langle 0,y^*\rangle$ (which equals $0$) is kept as on the page. The conjugate is taken with respect to the pairing of $F$ with $F^*$; no hypothesis beyond the standing ones and properness of $\bar h$ is assumed.
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 180, (6.2), proof of Theorem 6

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

/-- Rockafellar 1967, (6.2), p. 180: if the l.s.c. hull `h̄` is proper, then
`h̄(0) = sup_{y*} {⟨0, y*⟩ - h̄*(y*)}`. -/
theorem biconjugation_at_zero (P : Problem E E' F F')
    (hproper : Proper P.hull) :
    P.hull 0 = ⨆ y' : F', (P.pairF.pair (0 : F) y' : EReal) - P.hullConjugate y' := by sorry

end DualityStability.WeakDuality
