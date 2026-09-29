-- Prove2me | Theorems.Thm_EthierKurtz_hessian_posSemidef_of_isLocalMin
-- name    : EthierKurtz.hessian_posSemidef_of_isLocalMin
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-27T18:57:03.132993+00:00
-- url     : https://prove2.me/theorems/b6778fe3-8c56-48f7-8876-c0d22b11addf
-- title:
--   Hessian is positive-semidefinite at a local minimizer
-- statement:
--   This is the Hessian positive-semidefiniteness criterion at a local minimizer.
--
--   Let $d$ be a natural number, let $f : \mathrm{EuclideanSpace}(\mathbb{R}, \mathrm{Fin}\,d) \to \mathbb{R}$ be twice continuously differentiable, and suppose $f$ attains a local minimum at $x_0$. Then for every direction $v$, the Hessian quadratic form is nonnegative:
--
--   $$
--   \langle D^2 f(x_0) v, v \rangle \ge 0.
--   $$
--
--   Equivalently, the Hessian of $f$ at a local minimizer is a positive-semidefinite bilinear form. This is the key analytic input to maximum-principle arguments for second-order elliptic operators: at an interior minimum, the gradient vanishes and the second-order term has a sign, which is exactly what lets the operator inequality go through.
--
--   **Formalization Note** Lean has no separate Hessian matrix here; the quadratic form $\langle D^2 f(x_0) v, v \rangle$ is expressed as `(fderiv ℝ (fun y => fderiv ℝ f y v) x₀) v`, the derivative at $x_0$ in direction $v$ of the directional-derivative map $y \mapsto Df(y)(v)$.
-- source:
--   Second partial derivative test, necessary direction: at a local minimum the Hessian matrix is positive-semidefinite. https://en.wikipedia.org/wiki/Second_partial_derivative_test, discussion following the test statement.

import Mathlib
open scoped Topology

namespace EthierKurtz

theorem hessian_posSemidef_of_isLocalMin {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {x₀ : EuclideanSpace ℝ (Fin d)}
    (hf : ContDiff ℝ 2 f) (hmin : IsLocalMin f x₀)
    (v : EuclideanSpace ℝ (Fin d)) :
    0 ≤ (fderiv ℝ (fun y => fderiv ℝ f y v) x₀) v := by sorry

end EthierKurtz
