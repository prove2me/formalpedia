-- Prove2me | Theorems.Thm_DualityStability_StrongDuality_Supplement_theorem_4
-- name    : DualityStability.StrongDuality.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:47:16.626806+00:00
-- url     : https://prove2.me/theorems/770faa2d-7cb1-4b35-bba3-313040b2e058
-- title:
--   Theorem 4 — if (P) and (P*) are both stably set, both have solutions and $+\infty>\min(P)=\max(P^*)>-\infty$
-- statement:
--   Work in the standing setting of §3, with primal problem (P), minimize $f(x)-g(Ax)$, and dual problem $(P^*)$, maximize $g^*(y^*)-f^*(A^*y^*)$, with values $\inf(P)$ and $\sup(P^*)$.
--
--   **Theorem 4.** If (P) and (P\*) are both stably set, then both have solutions and
--
--   $$
--   +\infty>\min(P)=\max(P^*)>-\infty .
--   $$
--
--   That is: some $\bar x$ is a solution to (P) (it satisfies $\bar x\in C$, $A\bar x\in D$, and attains $\inf(P)$), some $\bar y^*$ is a solution to $(P^*)$ (it attains $\sup(P^*)$, which is not $-\infty$), and the common value $\inf(P)=\sup(P^*)$ is a real number.
--
--   Theorem 4 combines the two halves of Theorem 3 and is used in the proof of Theorem 8.
--
--   **Formalization Note** (P\*) stably set is the stability of its minimization form (P′), `StablySet p.dualH`, as in the published Theorem 3.
--
--   Differences from the source:
--   - encoding: properties of (P*) defined "in a dual manner" (pp. 173, 175, 181) → the same property of the minimization form (P′) of (P*), through its perturbation function `p.dualH` on $E^*$; reason: the paper's own dualization rule (P′), p. 173; identical to the published goal's convention
--   - encoding: extended-real values $[-\infty,+\infty]$ → `EReal`, with $\inf$/$\sup$ as `⨅`/`⨆`; reason: Lean convention; the same instances
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 179, Theorem 4

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

/-- Theorem 4, p. 179: if (P) and (P*) are both stably set, then both have solutions and
`+∞ > min (P) = max (P*) > -∞`. -/
theorem theorem_4 (p : Program E E' F F')
    (hP : StablySet p.h) (hD : StablySet p.dualH) :
    (∃ x : E, IsPrimalSolution p x) ∧ (∃ y' : F', IsDualSolution p y') ∧
      p.h 0 = p.dualValue ∧ p.h 0 ≠ ⊤ ∧ p.h 0 ≠ ⊥ := by sorry

end DualityStability.StrongDuality.Supplement
