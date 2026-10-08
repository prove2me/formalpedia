-- Prove2me | Theorems.Thm_DimCallCenters_Constraint_lemma_C_1
-- name    : DimCallCenters.Constraint.lemma_C_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:57:49.942666+00:00
-- url     : https://prove2.me/theorems/2f54b292-1d2d-4ca8-9d13-1e571d3f6044
-- title:
--   Lemma C.1 — G_λ is strictly convex and decreasing
-- statement:
--   Let $(\mu, D)$ be a wait model: $\mu > 0$, and for each $\lambda > 0$ the waiting-cost function $D_\lambda$ vanishes at $0$, is strictly increasing on $[0,\infty)$, and $D_\lambda(t)e^{-\theta t}$ is integrable on $(0,\infty)$ for every $\theta > 0$. Fix $\lambda > 0$ and let $G_\lambda(x) = \lambda\,G(\lambda/\mu + x\sqrt{\lambda/\mu}, \lambda)$ be the scaled waiting cost. Then
--
--   $$G_\lambda \text{ is strictly convex and strictly decreasing on } (0,\infty).$$
--
--   Monotonicity of $G_\lambda$ makes the continuous waiting cost $K_\lambda = \pi_\lambda G_\lambda$ decreasing, which links the integer constraint problem (31) to its continuous counterpart; convexity is used for the cost-minimization problem of the earlier sections.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 40, Appendix C, Lemma C.1

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_Glam

namespace DimCallCenters.Constraint

/-- Lemma C.1 (p. 40): for every arrival rate `λ > 0`, the scaled waiting cost `G_λ(·)` is
strictly convex and strictly decreasing on `(0, ∞)`. -/
theorem lemma_C_1 (M : DimCallCenters.Rationalized.WaitModel) (lam : ℝ) (hlam : 0 < lam) :
    StrictConvexOn ℝ (Set.Ioi 0) (DimCallCenters.Rationalized.Glam M lam) ∧ StrictAntiOn (DimCallCenters.Rationalized.Glam M lam) (Set.Ioi 0) := by sorry

end DimCallCenters.Constraint
