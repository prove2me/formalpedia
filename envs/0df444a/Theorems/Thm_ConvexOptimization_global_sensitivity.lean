-- Prove2me | Theorems.Thm_ConvexOptimization_global_sensitivity
-- name    : ConvexOptimization.global_sensitivity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-12T19:35:30.654727+00:00
-- url     : https://prove2.me/theorems/b310e71d-207a-4e3a-b9bf-24e65a3b54dd
-- title:
--   Global sensitivity inequality
-- statement:
--   **The global sensitivity inequality** — bound (5.57) of Boyd & Vandenberghe: optimal dual variables price the constraints.
--
--   Consider the standard problem and its perturbed version, in which the constraints are relaxed or tightened by $u \in \mathbb{R}^m$ and $v \in \mathbb{R}^p$:
--
--   $$f_i(x) \le u_i \ (i = 1,\dots,m), \qquad \langle a_j, x\rangle = b_j + v_j \ (j = 1,\dots,p).$$
--
--   Let $x^{\star}$ be feasible for the unperturbed problem and let $\lambda \succeq 0$, $\nu$ satisfy the zero-gap condition $g(\lambda,\nu) = f_0(x^{\star})$. Then every $x$ feasible for the $(u,v)$-perturbed problem satisfies
--
--   $$f_0(x) \;\ge\; f_0(x^{\star}) - \sum_{i=1}^{m}\lambda_i u_i - \sum_{j=1}^{p}\nu_j v_j .$$
--
--   Writing $p^{\star}(u,v)$ for the perturbed optimal value, this is $p^{\star}(u,v) \ge p^{\star}(0,0) - \lambda^{T}u - \nu^{T}v$: the multipliers bound how much can be gained by loosening a constraint. Loosening the $i$-th inequality by $u_i > 0$ cannot reduce the optimal value by more than $\lambda_i u_i$, so a large multiplier marks a constraint that is expensive to violate and a zero multiplier marks one that is locally free. Unlike the differential reading of shadow prices, the bound is *global* — valid for every perturbation, however large.
--
--   **Formalization Note** The statement quantifies over an arbitrary point $x$ feasible for the perturbed constraints rather than over the perturbed optimal value, which avoids assuming that optimal value exists; the zero-gap hypothesis is an equality of the `EReal`-valued dual function with the coercion of $f_0(x^{\star})$. Source: B&V §5.6.1, p. 250, eq. (5.57).
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 250, §5.6.1 eq. (5.57) (a global inequality relating the perturbed optimal value to the unperturbed one)

import Mathlib
import Definitions.Def_ConvexOptimization_lagrangeDuality

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.global_sensitivity {n mm p : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ)
    (fc : Fin mm → EuclideanSpace ℝ (Fin n) → ℝ)
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ feasibleSet fc a b)
    (lam : Fin mm → ℝ) (hlam : ∀ i, 0 ≤ lam i) (nu : Fin p → ℝ)
    (hzero : dualFunction f₀ fc a b lam nu = (f₀ xs : EReal))
    (u : Fin mm → ℝ) (v : Fin p → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (hx_ineq : ∀ i, fc i x ≤ u i) (hx_eq : ∀ j, ⟪a j, x⟫ = b j + v j) :
    f₀ xs - ∑ i, lam i * u i - ∑ j, nu j * v j ≤ f₀ x := by
  sorry
