-- Prove2me | Theorems.Thm_DimCallCenters_Rationalized_lemma_C_1
-- name    : DimCallCenters.Rationalized.lemma_C_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:18:11.330076+00:00
-- url     : https://prove2.me/theorems/afa3d5a4-02a6-4c9f-b214-a8302999d6ba
-- title:
--   Lemma C.1 — $G_\lambda$ is strictly convex decreasing
-- statement:
--   Let $(\mu, D_\lambda)$ satisfy the standing assumptions of Section 2 and fix $\lambda > 0$. Then the normalized waiting cost $G_\lambda(x) = \lambda G(N_\lambda(x),\lambda)$ is strictly convex and strictly decreasing on $(0,\infty)$:
--
--   $$x \mapsto G_\lambda(x) \text{ is strictly convex and strictly decreasing on } (0,\infty).$$
--
--   Together with convexity of $F$ and of $\pi_\lambda$, this gives the strict convexity of $C_\lambda$ that makes the continuous optimum $x^*_\lambda$ unique and the cost unimodal.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 40, Appendix C, Lemma C.1

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_Glam

namespace DimCallCenters.Rationalized

/-- Lemma C.1 (p. 40): for every arrival rate `λ > 0`, the normalized waiting cost
`G_λ(x) = λ G(N_λ(x), λ)` is strictly convex and strictly decreasing on `x ∈ (0, ∞)`. -/
theorem lemma_C_1 (M : WaitModel) (lam : ℝ) (hlam : 0 < lam) :
    StrictConvexOn ℝ (Set.Ioi 0) (Glam M lam) ∧ StrictAntiOn (Glam M lam) (Set.Ioi 0) := by sorry

end DimCallCenters.Rationalized
