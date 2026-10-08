-- Prove2me | Theorems.Thm_ALADIN_LocalStab_bound_from_partial_derivatives
-- name    : ALADIN.LocalStab.bound_from_partial_derivatives
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:46:06.992057+00:00
-- url     : https://prove2.me/theorems/41bc1cfb-2943-440e-8aaf-115077c210e5
-- title:
--   §7, proof of Lemma 3 — $\chi_1>\|\partial\xi/\partial x\|$, $\chi_2>\|\partial\xi/\partial\lambda\|$ give $\|\xi(x,\lambda)-\xi(x^*,\lambda^*)\|\le\chi_1\|x-x^*\|+\chi_2\|\lambda-\lambda^*\|$ locally
-- statement:
--   Let $X$, $\Lambda$, $Y$ be real normed spaces and let $\xi : X\times\Lambda\to Y$ be Fréchet differentiable at $(x^*,\lambda^*)$ with derivative $\xi'$. Write $\partial_x\xi(x^*,\lambda^*) = \xi'(\,\cdot\,,0)$ and $\partial_\lambda\xi(x^*,\lambda^*)=\xi'(0,\,\cdot\,)$ for the partial derivatives. If the constants $\chi_1,\chi_2$ satisfy
--   $$
--   \chi_1 > \big\|\partial_x\xi(x^*,\lambda^*)\big\|,\qquad \chi_2>\big\|\partial_\lambda\xi(x^*,\lambda^*)\big\|,
--   $$
--   then for all $(x,\lambda)$ in a neighbourhood of $(x^*,\lambda^*)$,
--   $$
--   \big\|\xi(x,\lambda)-\xi(x^*,\lambda^*)\big\| \;\le\; \chi_1\,\|x-x^*\| + \chi_2\,\|\lambda-\lambda^*\| .
--   $$
--
--   This is the last step of the proof of Lemma 3: applied to the parametric minimizers $\xi_i$ with $\xi_i(x^*,\lambda^*)=x^*_i$, it yields the inequality $\|y-x^*\|\le\chi_1\|x-x^*\|+\chi_2\|\lambda-\lambda^*\|$ of the lemma.
--
--   **Formalization Note** Stated for arbitrary real normed spaces; the partial derivatives are the composition of the derivative with the inclusions `ContinuousLinearMap.inl` and `ContinuousLinearMap.inr`, and their norms are operator norms. The paper writes $\partial\xi_i/\partial x_i$; the full partial derivative in $x$ is used here (the minimizer of block $i$ depends on $x$ only through $x_i$).
-- source:
--   Houska, Frasch, Diehl, An augmented Lagrangian based algorithm for distributed nonconvex optimization, SIAM J. Optim. 26 (2016), p. 1117, §7, proof of Lemma 3, last sentence (χ1 > ‖∂ξi/∂xi(x*, λ*)‖, χ2 > ‖∂ξi/∂λ(x*, λ*)‖)

import Mathlib

open Filter Topology

namespace ALADIN.LocalStab

/-- §7, proof of Lemma 3, p. 1117 (last step): if `ξ` is differentiable at `(x*, λ*)` and the
constants `χ₁`, `χ₂` exceed the norms of the partial derivatives `∂ξ/∂x (x*, λ*)` and
`∂ξ/∂λ (x*, λ*)`, then near `(x*, λ*)`
`‖ξ(x, λ) − ξ(x*, λ*)‖ ≤ χ₁ ‖x − x*‖ + χ₂ ‖λ − λ*‖`. -/
theorem bound_from_partial_derivatives {X Λ Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Λ] [NormedSpace ℝ Λ]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (ξ : X × Λ → Y) (ξ' : X × Λ →L[ℝ] Y) (xs : X) (lamS : Λ)
    (hξ : HasFDerivAt ξ ξ' (xs, lamS)) (χ₁ χ₂ : ℝ)
    (h₁ : ‖ξ'.comp (ContinuousLinearMap.inl ℝ X Λ)‖ < χ₁)
    (h₂ : ‖ξ'.comp (ContinuousLinearMap.inr ℝ X Λ)‖ < χ₂) :
    ∀ᶠ p in 𝓝 (xs, lamS), ‖ξ p - ξ (xs, lamS)‖ ≤ χ₁ * ‖p.1 - xs‖ + χ₂ * ‖p.2 - lamS‖ := by sorry

end ALADIN.LocalStab
