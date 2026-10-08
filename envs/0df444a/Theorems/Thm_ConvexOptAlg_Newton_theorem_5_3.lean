-- Prove2me | Theorems.Thm_ConvexOptAlg_Newton_theorem_5_3
-- name    : ConvexOptAlg.Newton.theorem_5_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:33:59.274059+00:00
-- url     : https://prove2.me/theorems/549be4bf-ed5f-4c28-80e8-44b25b3041f7
-- title:
--   Theorem 5.3, p. 320 — from ‖x₀ − x*‖ ≤ μ/(2M), Newton's method is well defined and ‖x_{k+1} − x*‖ ≤ (M/μ)‖x_k − x*‖²
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be a $C^2$ function whose Hessian is $M$-Lipschitz in operator norm, $\|\nabla^2 f(x)-\nabla^2 f(y)\|\le M\|x-y\|$ for all $x,y$, with $M>0$. Let $x^*$ be a local minimum of $f$ with strictly positive Hessian, $\nabla^2 f(x^*)\succeq\mu I_n$ for some $\mu>0$. Suppose the starting point $x_0$ satisfies
--
--   $$\|x_0-x^*\|\le\frac{\mu}{2M}.$$
--
--   Then Newton's method started at $x_0$ is well defined: there is exactly one sequence $(x_k)_{k\ge0}$ with first term $x_0$ satisfying $\nabla^2 f(x_k)(x_k-x_{k+1})=\nabla f(x_k)$ for all $k$, and along it every Hessian $\nabla^2 f(x_k)$ is invertible, so that $x_{k+1}=x_k-[\nabla^2 f(x_k)]^{-1}\nabla f(x_k)$. Moreover the iterates converge to $x^*$ at a quadratic rate:
--
--   $$\|x_{k+1}-x^*\|\le\frac M\mu\,\|x_k-x^*\|^2\qquad\text{for all }k\ge0,\qquad x_k\to x^* .$$
--
--   This is the classical local quadratic convergence of Newton's method: close enough to a nondegenerate local minimum, the number of correct digits roughly doubles at every step. It is the starting point of the interior point methods of §5.3, which keep Newton's method inside such a region of fast convergence.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`; the gradient and Hessian are explicit maps tied to $f$ (definition item), and the Hessian condition at $x^*$ is the quadratic-form inequality $\langle\nabla^2 f(x^*)v,v\rangle\ge\mu\|v\|^2$. "Well-defined" is formalized as unique existence of a Newton run from $x_0$ together with invertibility (bijectivity) of every Hessian along every such run; the quadratic rate and the convergence are asserted for every Newton run from $x_0$. $M>0$ is a disclosed implicit hypothesis (the radius $\mu/(2M)$ divides by $M$; with $M=0$ Lean's $\mu/0=0$ would force $x_0=x^*$). Convexity of $f$ is not assumed, as on the page.
-- source:
--   Bubeck, Convex Optimization: Algorithms and Complexity, arXiv:1405.4980v2, Theorem 5.3, p. 320

import Mathlib
import Definitions.Def_ConvexOptAlg_Newton_Defs

namespace ConvexOptAlg.Newton

open Filter Topology

/-- **Theorem 5.3** (Bubeck, arXiv:1405.4980v2, p. 320). Let `f : ℝⁿ → ℝ` be C² with gradient map
`g` and Hessian map `H`, and assume the Hessian is `M`-Lipschitz in operator norm. Let `x∗` be a
local minimum of `f` with `∇²f(x∗) ⪰ μ Iₙ`, `μ > 0`, i.e. `μ‖v‖² ≤ ⟪∇²f(x∗) v, v⟫` for all `v`.
If `‖x₀ − x∗‖ ≤ μ/(2M)`, then Newton's method started at `x₀` is well-defined — there is exactly one
Newton run from `x₀`, and along every Newton run from `x₀` each Hessian `∇²f(x_k)` is invertible —
and it converges to `x∗` at a quadratic rate: `‖x_{k+1} − x∗‖ ≤ (M/μ)‖x_k − x∗‖²` for every `k ≥ 0`.
`0 < M` is a disclosed implicit hypothesis (the radius `μ/(2M)` divides by `M`). -/
theorem theorem_5_3 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hfgH : IsC2GradHess f g H) (M μ : ℝ) (hM : 0 < M) (hHL : IsLipschitzHessian H M)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : IsLocalMin f xstar) (hμ : 0 < μ)
    (hHstar : ∀ v : EuclideanSpace ℝ (Fin n), μ * ‖v‖ ^ 2 ≤ inner ℝ (H xstar v) v)
    (x0 : EuclideanSpace ℝ (Fin n)) (hx0 : ‖x0 - xstar‖ ≤ μ / (2 * M)) :
    (∃! x : ℕ → EuclideanSpace ℝ (Fin n), x 0 = x0 ∧ IsNewtonRun g H x) ∧
    ∀ x : ℕ → EuclideanSpace ℝ (Fin n), x 0 = x0 → IsNewtonRun g H x →
      (∀ k, Function.Bijective (H (x k))) ∧
      (∀ k, ‖x (k + 1) - xstar‖ ≤ M / μ * ‖x k - xstar‖ ^ 2) ∧
      Tendsto x atTop (𝓝 xstar) := by sorry

end ConvexOptAlg.Newton
