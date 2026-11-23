-- Prove2me | Theorems.Thm_DualityStability_StrongDuality_Supplement_theorem_7
-- name    : DualityStability.StrongDuality.Supplement.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:50:44.441811+00:00
-- url     : https://prove2.me/theorems/24f3a324-9123-4a0a-b931-3f77af0b7eca
-- title:
--   Theorem 7 — (P) normal with finite value iff (P*) normal with finite value; then $\inf(P)=\sup(P^*)$, which in turn implies both are normal
-- statement:
--   Work in the standing setting of §3 with perturbation function $h(z)=\inf(P(z))$ of (P). (P) is normal when $h$ is lower semicontinuous at $0$, $\inf(P)=\liminf_{z\to0}h(z)$, and (P\*) is normal in the dual manner, through its minimization form $(P')$.
--
--   **Theorem 7.**
--
--   1. (P) is normal and $\inf(P)$ is finite, if and only if $(P^*)$ is normal and $\sup(P^*)$ is finite.
--   2. In that case
--   $$
--   \inf(P)=\sup(P^*).
--   $$
--   3. Conversely, $\inf(P)=\sup(P^*)$ (whatever the common value in $[-\infty,+\infty]$) implies that both (P) and $(P^*)$ are normal.
--
--   Theorem 7 identifies normality as exactly the absence of a duality gap. It is a corollary of Theorem 6 and its dual.
--
--   **Formalization Note** Normality of (P) uses `Filter.liminf p.h (nhds 0)` (unpunctured, as in (2.1)); normality of (P\*) is that of (P′) on `p.dualH` over `nhds (0 : E')`. Part 3 carries no finiteness hypothesis.
--
--   Differences from the source:
--   - encoding: properties of (P*) defined "in a dual manner" (pp. 173, 175, 181) → the same property of the minimization form (P′) of (P*), through its perturbation function `p.dualH` on $E^*$; reason: the paper's own dualization rule (P′), p. 173; identical to the published goal's convention
--   - encoding: extended-real values $[-\infty,+\infty]$ → `EReal`, with $\inf$/$\sup$ as `⨅`/`⨆`; reason: Lean convention; the same instances
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 181, Theorem 7 and (6.4)

import Definitions.Def_DualityStability_StrongDuality_Supplement_Normal

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

/-- Theorem 7, p. 181: (P) is normal with `inf (P)` finite iff (P*) is normal with
`sup (P*)` finite; in that case `inf (P) = sup (P*)`; conversely `inf (P) = sup (P*)`
implies that (P) and (P*) are both normal. -/
theorem theorem_7 (p : Program E E' F F') :
    ((PrimalNormal p ∧ p.h 0 ≠ ⊤ ∧ p.h 0 ≠ ⊥) ↔
        (DualNormal p ∧ p.dualValue ≠ ⊤ ∧ p.dualValue ≠ ⊥)) ∧
      ((PrimalNormal p ∧ p.h 0 ≠ ⊤ ∧ p.h 0 ≠ ⊥) → p.h 0 = p.dualValue) ∧
      (p.h 0 = p.dualValue → PrimalNormal p ∧ DualNormal p) := by sorry

end DualityStability.StrongDuality.Supplement
