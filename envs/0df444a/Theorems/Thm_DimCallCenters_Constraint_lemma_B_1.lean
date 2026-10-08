-- Prove2me | Theorems.Thm_DimCallCenters_Constraint_lemma_B_1
-- name    : DimCallCenters.Constraint.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:57:57.483894+00:00
-- url     : https://prove2.me/theorems/9fdf2f8b-8fb3-4215-8689-94e0f74d2fbf
-- title:
--   Lemma B.1 — the Halfin–Whitt delay function P is strictly convex and decreasing
-- statement:
--   Let $P(x) = 1/(1 + x/h(-x))$ be the Halfin–Whitt delay function, with $h = \phi/(1-\Phi)$ the hazard rate of the standard normal distribution. Then
--
--   $$P \text{ is strictly convex and strictly decreasing on } (0,\infty).$$
--
--   Monotonicity of $P$ is what makes the staffing equations $P(y)G_\lambda(y) = M_\lambda$ of Section 8 have at most one solution, and it underlies the asymptotic comparisons (15)–(17).
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 39, Appendix B, Lemma B.1

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_delayFn

namespace DimCallCenters.Constraint

/-- Lemma B.1 (p. 39): the Halfin–Whitt delay function `P(·)` is strictly convex and strictly
decreasing on `(0, ∞)`. -/
theorem lemma_B_1 :
    StrictConvexOn ℝ (Set.Ioi 0) DimCallCenters.Rationalized.delayFn ∧ StrictAntiOn DimCallCenters.Rationalized.delayFn (Set.Ioi 0) := by sorry

end DimCallCenters.Constraint
