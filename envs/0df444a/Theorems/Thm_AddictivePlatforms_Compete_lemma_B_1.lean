-- Prove2me | Theorems.Thm_AddictivePlatforms_Compete_lemma_B_1
-- name    : AddictivePlatforms.Compete.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T12:57:42.004846+00:00
-- url     : https://prove2.me/theorems/6142475c-5bd4-454c-93ad-90a1f6001781
-- title:
--   Lemma B.1, p. 28 — u(x) − xu′(x) is strictly increasing for increasing, strictly concave, differentiable u on ℝ₊
-- statement:
--   Let $u : \mathbb{R}_+ \to \mathbb{R}$ be increasing, strictly concave and differentiable. Then the function
--   $$x \longmapsto u(x) - x\,u'(x)$$
--   is strictly increasing on $\mathbb{R}_+$.
--
--   Geometrically, $u(x) - x u'(x)$ is the intercept at $0$ of the tangent line to $u$ at $x$; for a strictly concave function this intercept rises as the point of tangency moves right. In the paper it is the marginal value of an additional (fractional) platform, and the lemma drives the concavity statements of Lemmas B.2 and B.3.
--
--   **Formalization Note.** $u$ is a function on $\mathbb{R}$ of which only the restriction to $[0,\infty)$ matters; monotonicity, strict concavity and differentiability are required on $[0,\infty)$, and $u'(x)$ is the derivative within $[0,\infty)$ (one-sided at $0$).
-- source:
--   Ichihashi & Kim, Addictive Platforms, Bank of Canada SWP 2022-16 (Apr. 1, 2022), p. 28, Lemma B.1

import Mathlib

open Set

namespace AddictivePlatforms.Compete

/-- Lemma B.1 (p. 28): for an increasing, strictly concave, differentiable `u : ℝ₊ → ℝ`,
`u(x) − x u′(x)` is strictly increasing on `ℝ₊` (the derivative is one-sided at `0`). -/
theorem lemma_B_1 (u : ℝ → ℝ) (hmono : MonotoneOn u (Ici 0))
    (hconc : StrictConcaveOn ℝ (Ici 0) u) (hdiff : DifferentiableOn ℝ u (Ici 0)) :
    StrictMonoOn (fun x => u x - x * derivWithin u (Ici 0) x) (Ici 0) := by sorry

end AddictivePlatforms.Compete
