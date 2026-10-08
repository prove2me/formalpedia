-- Prove2me | Theorems.Thm_ConvexOptAlg_Newton_lipschitz_integral_bound
-- name    : ConvexOptAlg.Newton.lipschitz_integral_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:33:28.81948+00:00
-- url     : https://prove2.me/theorems/f840e04c-8f67-4dd6-85e3-692b80ef8f6c
-- title:
--   §5.3.2, proof of Theorem 5.3, p. 321 — ∫₀¹ ‖∇²f(x_k) − ∇²f(x* + s(x_k − x*))‖ ds ≤ (M/2)‖x_k − x*‖
-- statement:
--   Let $H:\mathbb R^n\to L(\mathbb R^n,\mathbb R^n)$ be $M$-Lipschitz in operator norm, i.e. $\|H(x)-H(y)\|\le M\|x-y\|$ for all $x,y$ (for instance, the Hessian $H=\nabla^2 f$ of a function with $M$-Lipschitz Hessian). Then for all $x^*,y\in\mathbb R^n$,
--
--   $$\int_0^1\big\|H(y)-H\big(x^*+s(y-x^*)\big)\big\|\,ds\le\frac M2\,\|y-x^*\|.$$
--
--   In the analysis of Newton's method, with $H=\nabla^2 f$ and $y=x_k$, this bounds the integral in the error representation of a Newton step by $\frac M2\|x_k-x^*\|$, which produces the quadratic rate.
--
--   **Formalization Note** The book states the bound at an iterate $x_k$ for the Hessian of $f$; it uses only the Lipschitz property, so it is stated for any $M$-Lipschitz map $H$ and any point $y$. No sign condition on $M$ is needed (a negative $M$ makes the hypothesis unsatisfiable unless $n=0$). $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` and $\|\cdot\|$ on linear maps is the operator norm.
-- source:
--   Bubeck, arXiv:1405.4980v2, §5.3.2, proof of Theorem 5.3, p. 321, fifth display

import Mathlib
import Definitions.Def_ConvexOptAlg_Newton_Defs

namespace ConvexOptAlg.Newton

/-- The Lipschitz integral bound in the proof of Theorem 5.3 (Bubeck, arXiv:1405.4980v2, §5.3.2,
p. 321, fifth display of the proof): if the Hessian map `H` is `M`-Lipschitz in operator norm, then
for all points `x∗, y ∈ ℝⁿ`,
`∫₀¹ ‖∇²f(y) − ∇²f(x∗ + s(y − x∗))‖ ds ≤ (M/2)‖y − x∗‖`.
The book states it at `y = x_k`; it uses only the Lipschitz property, so it is stated for any
`M`-Lipschitz map `H : ℝⁿ → L(ℝⁿ, ℝⁿ)` and any `y`. -/
theorem lipschitz_integral_bound {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (M : ℝ) (hHL : IsLipschitzHessian H M) (xstar y : EuclideanSpace ℝ (Fin n)) :
    ∫ s in (0 : ℝ)..1, ‖H y - H (xstar + s • (y - xstar))‖ ≤ M / 2 * ‖y - xstar‖ := by sorry

end ConvexOptAlg.Newton
