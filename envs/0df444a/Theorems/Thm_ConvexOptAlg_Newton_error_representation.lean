-- Prove2me | Theorems.Thm_ConvexOptAlg_Newton_error_representation
-- name    : ConvexOptAlg.Newton.error_representation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:33:34.983585+00:00
-- url     : https://prove2.me/theorems/08af044d-4770-4eab-bb9c-23d311d70184
-- title:
--   §5.3.2, proof of Theorem 5.3, p. 321 — ∇²f(x_k)(x_{k+1} − x*) = ∫₀¹ [∇²f(x_k) − ∇²f(x* + s(x_k − x*))](x_k − x*) ds
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be a $C^2$ function with gradient $\nabla f$ and Hessian $\nabla^2 f$, and let $x^*$ be a local minimum of $f$, so that $\nabla f(x^*)=0$. Let $y\in\mathbb R^n$. Then
--
--   1. the gradient at $y$ is
--   $$\nabla f(y)=\int_0^1\nabla^2 f\big(x^*+s(y-x^*)\big)\,(y-x^*)\,ds;$$
--
--   2. if $y^+$ is obtained from $y$ by a Newton step, i.e. $\nabla^2 f(y)\,(y-y^+)=\nabla f(y)$, then
--   $$\nabla^2 f(y)\,(y^+-x^*)=\int_0^1\Big[\nabla^2 f(y)-\nabla^2 f\big(x^*+s(y-x^*)\big)\Big](y-x^*)\,ds.$$
--
--   With $y=x_k$ and $y^+=x_{k+1}$ this is the representation of the error of one Newton step from which the quadratic rate is read off.
--
--   **Formalization Note** The book writes part 2 as $x_{k+1}-x^*=[\nabla^2 f(x_k)]^{-1}\int_0^1[\dots](x_k-x^*)\,ds$. Here both sides are multiplied by $\nabla^2 f(y)$, so no inverse is taken; when $\nabla^2 f(y)$ is invertible the two forms are equivalent. The statement is for any point $y$ and any Newton step $y^+$ from it, not only for iterates of a run. Integrals are Bochner integrals over $[0,1]$ of $\mathbb R^n$-valued maps.
-- source:
--   Bubeck, arXiv:1405.4980v2, §5.3.2, proof of Theorem 5.3, p. 321, second and third displays

import Mathlib
import Definitions.Def_ConvexOptAlg_Newton_Defs

namespace ConvexOptAlg.Newton

/-- The error representation in the proof of Theorem 5.3 (Bubeck, arXiv:1405.4980v2, §5.3.2,
p. 321, second and third displays of the proof). Let `f : ℝⁿ → ℝ` be C² with gradient map `g` and
Hessian map `H`, and let `x∗` be a local minimum of `f` (so `∇f(x∗) = 0`). For every point `y`:
(1) `∇f(y) = ∫₀¹ ∇²f(x∗ + s(y − x∗)) (y − x∗) ds`; and
(2) if `y⁺` is a Newton step from `y`, i.e. `∇²f(y)(y − y⁺) = ∇f(y)`, then
`∇²f(y)(y⁺ − x∗) = ∫₀¹ [∇²f(y) − ∇²f(x∗ + s(y − x∗))] (y − x∗) ds`.
Part (2) is the page's last line `x_{k+1} − x∗ = [∇²f(x_k)]⁻¹ ∫₀¹ […] (x_k − x∗) ds` with both
sides multiplied by `∇²f(x_k)`, which avoids inverting a possibly singular operator; for the
book's iterate (`y = x_k`, `y⁺ = x_{k+1}`, `∇²f(x_k)` invertible) the two forms are equivalent. -/
theorem error_representation {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hfgH : IsC2GradHess f g H) (xstar : EuclideanSpace ℝ (Fin n)) (hmin : IsLocalMin f xstar)
    (y yplus : EuclideanSpace ℝ (Fin n)) (hstep : H y (y - yplus) = g y) :
    g y = (∫ s in (0 : ℝ)..1, H (xstar + s • (y - xstar)) (y - xstar)) ∧
    H y (yplus - xstar) =
      ∫ s in (0 : ℝ)..1, (H y - H (xstar + s • (y - xstar))) (y - xstar) := by sorry

end ConvexOptAlg.Newton
