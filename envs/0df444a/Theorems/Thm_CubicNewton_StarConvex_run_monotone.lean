-- Prove2me | Theorems.Thm_CubicNewton_StarConvex_run_monotone
-- name    : CubicNewton.StarConvex.run_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:24:40.81088+00:00
-- url     : https://prove2.me/theorems/e65e3af1-7227-4379-b66c-f95f96453001
-- title:
--   Method (3.3) is monotone: $f(x_{k+1})\le f(x_k)$
-- statement:
--   Let $x_0, x_1, \dots$ with parameters $M_0, M_1, \dots$ be any run of the cubic regularization of Newton method (3.3): $x_{k+1} = T_{M_k}(x_k)$ is a global minimizer of the cubic model at $x_k$, and $f(x_{k+1}) \le \bar f_{M_k}(x_k)$. Then the function values never increase:
--
--   $$f(x_{k+1}) \le f(x_k) \qquad \text{for all } k \ge 0.$$
--
--   The paper derives this from $\bar f_M(x) \le f(x)$. Monotonicity keeps every iterate in the level set $\{x : f(x) \le f(x_0)\}$, hence in $F$, which is what lets the Section 2 estimates be applied at every iteration.
--
--   **Formalization Note** The statement needs only the run predicate; it holds for any gradient and Hessian maps and any parameters, which makes it a slightly stronger statement than the remark in its context.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 184, Section 3 (remark after method (3.3))

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicNewtonRun

namespace CubicNewton.StarConvex

/-- Nesterov–Polyak 2006, Section 3, p. 184 (remark after method (3.3)): since `f̄_M(x) ≤ f(x)`,
every run of the cubic regularization of Newton method (3.3) is monotone,
`f(x_{k+1}) ≤ f(x_k)` for all `k ≥ 0`. -/
theorem run_monotone {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L₀ L : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (M : ℕ → ℝ) (hrun : CubicNewton.Shared.IsCubicNewtonRun f g H L₀ L x₀ x M) :
    ∀ k, f (x (k + 1)) ≤ f (x k) := by sorry

end CubicNewton.StarConvex
