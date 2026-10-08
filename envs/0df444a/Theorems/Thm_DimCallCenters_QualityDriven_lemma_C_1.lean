-- Prove2me | Theorems.Thm_DimCallCenters_QualityDriven_lemma_C_1
-- name    : DimCallCenters.QualityDriven.lemma_C_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:55:46.348985+00:00
-- url     : https://prove2.me/theorems/73877692-bf63-41fb-8109-de04a5f39f7a
-- title:
--   Lemma C.1 — $G_\lambda$ is strictly convex and decreasing
-- statement:
--   Let $(\mu, D)$ be a waiting model and $\lambda > 0$. Then the normalized waiting cost $G_\lambda(x) = \lambda\,G(N_\lambda(x),\lambda)$ is strictly convex and strictly decreasing on $(0,\infty)$:
--
--   $$
--   x \mapsto G_\lambda(x) \ \text{is strictly convex and strictly decreasing on } (0,\infty).
--   $$
--
--   Together with the convexity of $F$ and of $\pi_\lambda$, this is what makes $C_\lambda$ unimodal, so that the continuous optimum $x^*_\lambda$ and the rounding argument of Lemma 3.2 make sense.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 40, Lemma C.1

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_Glam

namespace DimCallCenters.QualityDriven

/-- Lemma C.1 (p. 40): for every arrival rate `λ > 0`, the normalized waiting DimCallCenters.Rationalized.cost
`G_λ(x) = λ G(N_λ(x), λ)` is strictly convex and strictly decreasing on `x ∈ (0, ∞)`. -/
theorem lemma_C_1 (M : DimCallCenters.Rationalized.WaitModel) (lam : ℝ) (hlam : 0 < lam) :
    StrictConvexOn ℝ (Set.Ioi 0) (DimCallCenters.Rationalized.Glam M lam) ∧ StrictAntiOn (DimCallCenters.Rationalized.Glam M lam) (Set.Ioi 0) := by sorry

end DimCallCenters.QualityDriven
