-- Prove2me | Theorems.Thm_ConvexOptAlg_Newton_hessian_lower_bound
-- name    : ConvexOptAlg.Newton.hessian_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:33:52.248329+00:00
-- url     : https://prove2.me/theorems/43c6bbf9-85ed-4c15-94e4-fdfa96f738f2
-- title:
--   §5.3.2, proof of Theorem 5.3, p. 321 — ∇²f(x_k) ⪰ ∇²f(x*) − M‖x_k − x*‖Iₙ ⪰ (μ − M‖x_k − x*‖)Iₙ ⪰ (μ/2)Iₙ
-- statement:
--   Let $H:\mathbb R^n\to L(\mathbb R^n,\mathbb R^n)$ be $M$-Lipschitz in operator norm with $M>0$, and let $x^*\in\mathbb R^n$ satisfy $H(x^*)\succeq\mu I_n$ with $\mu>0$, that is, $\langle H(x^*)v,v\rangle\ge\mu\|v\|^2$ for all $v$. Then for every $y\in\mathbb R^n$ and every $v\in\mathbb R^n$:
--
--   1. $\langle H(y)v,v\rangle\ge\langle H(x^*)v,v\rangle-M\|y-x^*\|\,\|v\|^2$;
--   2. $\langle H(y)v,v\rangle\ge(\mu-M\|y-x^*\|)\,\|v\|^2$;
--   3. if $\|y-x^*\|\le\frac{\mu}{2M}$, then $\langle H(y)v,v\rangle\ge\frac{\mu}{2}\|v\|^2$.
--
--   In Loewner-order notation, with $H=\nabla^2 f$ and $y=x_k$,
--
--   $$\nabla^2 f(x_k)\succeq\nabla^2 f(x^*)-M\|x_k-x^*\|I_n\succeq(\mu-M\|x_k-x^*\|)I_n\succeq\frac\mu2 I_n .$$
--
--   This keeps the Hessian uniformly positive definite on the ball of radius $\mu/(2M)$ around $x^*$, so Newton's method is well defined there and the inverse Hessian has operator norm at most $2/\mu$.
--
--   **Formalization Note** $A\succeq cI_n$ is read as the quadratic-form inequality $\langle Av,v\rangle\ge c\|v\|^2$ for all $v$. The statement uses only the Lipschitz property and the hypothesis at $x^*$, so it is stated for any $M$-Lipschitz map $H$; symmetry of the Hessian is not needed for these inequalities. $M>0$ is a disclosed implicit hypothesis: the radius $\mu/(2M)$ divides by $M$.
-- source:
--   Bubeck, arXiv:1405.4980v2, §5.3.2, proof of Theorem 5.3, p. 321, last display

import Mathlib
import Definitions.Def_ConvexOptAlg_Newton_Defs

namespace ConvexOptAlg.Newton

/-- The Hessian lower bound in the proof of Theorem 5.3 (Bubeck, arXiv:1405.4980v2, §5.3.2,
p. 321, last display of the proof). Let `H : ℝⁿ → L(ℝⁿ, ℝⁿ)` be `M`-Lipschitz in operator norm,
`M > 0`, and let `∇²f(x∗) ⪰ μ Iₙ` with `μ > 0`, i.e. `μ‖v‖² ≤ ⟪∇²f(x∗) v, v⟫` for all `v`. Then for
every `y ∈ ℝⁿ`, in the order of the page's chain
`∇²f(y) ⪰ ∇²f(x∗) − M‖y − x∗‖Iₙ ⪰ (μ − M‖y − x∗‖)Iₙ ⪰ (μ/2)Iₙ`:
(1) `⟪∇²f(x∗) v, v⟫ − M‖y − x∗‖‖v‖² ≤ ⟪∇²f(y) v, v⟫` for all `v`;
(2) `(μ − M‖y − x∗‖)‖v‖² ≤ ⟪∇²f(y) v, v⟫` for all `v`;
(3) if `‖y − x∗‖ ≤ μ/(2M)`, then `(μ/2)‖v‖² ≤ ⟪∇²f(y) v, v⟫` for all `v`.
Loewner order `A ⪰ c Iₙ` is read as the quadratic-form inequality. -/
theorem hessian_lower_bound {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (M μ : ℝ) (hM : 0 < M) (hμ : 0 < μ) (hHL : IsLipschitzHessian H M)
    (xstar : EuclideanSpace ℝ (Fin n))
    (hHstar : ∀ v : EuclideanSpace ℝ (Fin n), μ * ‖v‖ ^ 2 ≤ inner ℝ (H xstar v) v)
    (y : EuclideanSpace ℝ (Fin n)) :
    (∀ v : EuclideanSpace ℝ (Fin n),
        inner ℝ (H xstar v) v - M * ‖y - xstar‖ * ‖v‖ ^ 2 ≤ inner ℝ (H y v) v) ∧
    (∀ v : EuclideanSpace ℝ (Fin n), (μ - M * ‖y - xstar‖) * ‖v‖ ^ 2 ≤ inner ℝ (H y v) v) ∧
    (‖y - xstar‖ ≤ μ / (2 * M) →
      ∀ v : EuclideanSpace ℝ (Fin n), μ / 2 * ‖v‖ ^ 2 ≤ inner ℝ (H y v) v) := by sorry

end ConvexOptAlg.Newton
